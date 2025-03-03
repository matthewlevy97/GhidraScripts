//TODO write a description for this script
//@author 
//@category _NEW_
//@keybinding 
//@menupath 
//@toolbar 
//@runtime Java

import java.io.File;
import java.io.FileWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonObject;
import com.google.gson.stream.JsonWriter;

import ghidra.app.decompiler.DecompInterface;
import ghidra.app.decompiler.DecompileResults;
import ghidra.app.script.GhidraScript;
import ghidra.features.base.values.GhidraValuesMap;
import ghidra.program.model.sourcemap.*;
import ghidra.program.model.lang.protorules.*;
import ghidra.program.model.mem.*;
import ghidra.program.model.lang.*;
import ghidra.program.model.pcode.*;
import ghidra.program.model.data.ISF.*;
import ghidra.program.model.util.*;
import ghidra.util.SystemUtilities;
import ghidra.program.model.reloc.*;
import ghidra.program.model.data.*;
import ghidra.program.model.block.*;
import ghidra.program.model.symbol.*;
import ghidra.program.model.scalar.*;
import ghidra.program.model.listing.*;
import ghidra.program.model.address.*;

// TODO: Make Headless better supported
// TODO: Add checks for FORTIFY_SOURCE
// TODO: Add check for stack clash protection
// TODO: Add check for auto-var-init

enum SearchedFunction {
	INVALID,
	
	// ___stack_chk_fail
	STACK_CHK_FAIL,
	
	// memcpy
	MEMCPY,
	MEMCPY_FORTIFIED,
	
	// mempcpy
	MEMPCPY,
	MEMPCPY_FORTIFIED,
	
	// memmove
	MEMMOVE,
	MEMMOVE_FORTIFIED,
	
	// memset
	MEMSET,
	MEMSET_FORTIFIED,
	
	// strcpy
	STRCPY,
	STRCPY_FORTIFIED,
	
	// stpcpy
	STPCPY,
	STPCPY_FORTIFIED,
	
	// strncpy
	STRNCPY,
	STRNCPY_FORTIFIED,
	
	// strcat
	STRCAT,
	STRCAT_FORTIFIED,
	
	// strncat
	STRNCAT,
	STRNCAT_FORTIFIED,
	
	// sprintf
	SPRINTF,
	SPRINTF_FORTIFIED,
	
	// vsprintf
	VSPRINTF,
	VSPRINTF_FORTIFIED,
	
	// snprintf
	SNPRINTF,
	SNPRINTF_FORTIFIED,
	
	// vsnprintf
	VSNPRINTF,
	VSNPRINTF_FORTIFIED,
	
	// gets
	GETS;
	
	// TODO: Optimize this via Trie
	public static SearchedFunction Find(String funcName) {
		if (funcName.equals("___stack_chk_fail")) {
			return STACK_CHK_FAIL;
		} else if (funcName.startsWith("_memcpy")) {
			return MEMCPY;
		} else if (funcName.equals("___memcpy_chk")) {
			return MEMCPY_FORTIFIED;
		} else if (funcName.startsWith("_mempcpy")) {
			return MEMPCPY;
		} else if (funcName.startsWith("___mempcpy_chk")) {
			return MEMPCPY_FORTIFIED;
		} else if (funcName.startsWith("_memmove")) {
			return MEMMOVE;
		} else if (funcName.startsWith("___memmove_chk")) {
			return MEMMOVE_FORTIFIED;
		} else if (funcName.startsWith("_memset")) {
			return MEMSET;
		} else if (funcName.startsWith("___memset_chk")) {
			return MEMSET_FORTIFIED;
		} else if (funcName.startsWith("_strcpy")) {
			return STRCPY;
		} else if (funcName.startsWith("___strcpy_chk")) {
			return STRCPY_FORTIFIED;
		} else if (funcName.startsWith("_stpcpy")) {
			return STPCPY;
		} else if (funcName.startsWith("___stpcpy_chk")) {
			return STPCPY_FORTIFIED;
		} else if (funcName.startsWith("_strncpy")) {
			return STRNCPY;
		} else if (funcName.startsWith("___strncpy_chk")) {
			return STRNCPY_FORTIFIED;
		} else if (funcName.startsWith("_strcat")) {
			return STRCAT;
		} else if (funcName.startsWith("___strcat_chk")) {
			return STRCAT_FORTIFIED;
		} else if (funcName.startsWith("_strncat")) {
			return STRNCAT;
		} else if (funcName.startsWith("___strncat_chk")) {
			return STRNCAT_FORTIFIED;
		} else if (funcName.startsWith("_sprintf")) {
			return SPRINTF;
		} else if (funcName.startsWith("___sprintf_chk")) {
			return SPRINTF_FORTIFIED;
		} else if (funcName.startsWith("_vsprintf")) {
			return VSPRINTF;
		} else if (funcName.startsWith("___vsprintf_chk")) {
			return VSPRINTF_FORTIFIED;
		} else if (funcName.startsWith("_snprintf")) {
			return SNPRINTF;
		} else if (funcName.startsWith("___snprintf_chk")) {
			return SNPRINTF_FORTIFIED;
		} else if (funcName.startsWith("_vsnprintf")) {
			return VSNPRINTF;
		} else if (funcName.startsWith("___vsnprintf_chk")) {
			return VSNPRINTF_FORTIFIED;
		} else if (funcName.startsWith("_gets")) {
			return GETS;
		}
		return INVALID;
	}
};

class FunctionMitigations {
    /**
	 * Use rules to determine if stack protector should be enabled
	 * If enabled/should be enabled, can we determine which level?
	 * 
	 * Stack Protector:
	 * 	- Character array >8 bytes
	 * 	- 8-bit integer array >8 bytes
	 * 	- Call to `alloca()` with variable size or constant size >8 bytes
	 * 
	 * Stack Protector All:
	 * 	- Added to ALL functions
	 * 
	 * Stack Protector Strong:
	 * 	- Array of any size/type
	 * 	- Call to `alloca()`
	 * 	- Local variable that has its address taken
	 */
	public boolean stackCanaryEnabled;
	public boolean stackCanaryBasicSupport;
	public boolean stackCanaryStrongSupport;
	
	/**
	 * LibCXX (LLVM) uses ABI tagging to handle different implementations
	 * of STL objects due to everything being compile-time header-only
	 * template classes.
	 * 
	 * LLVM implementation for "hardened" or bound-checked vectors
	 * adds a compile time `#ifdef` that calls the vector's `size()`
	 * function before any access (e.g., `operator[]`) to verify
	 * bounds. Recording every vector ABI and checking if they
	 * call `size()` quickly identifies enablement.
	 * 
	 * NOTE: vector is not the only STL object that can be hardened,
	 * but it is the only one checked.
	 */
	public Set<String> libCXXHardenedABINot;
	public Set<String> libCXXHardenedABI;
	
	/**
	 * Fortify Source Functions:
	 * 	memcpy, mempcpy, memmove, memset, strcpy, stpcpy, strncpy, strcat, 
	 * 	strncat, sprintf, vsprintf, snprintf, vsnprintf, gets
	 * 
	 * Normal version is embedded as `_XXX` while the fortified version
	 * is `___XXX_chk`.
	 */
	boolean memcpy, memcpyFortified;
	boolean mempcpy, mempcpyFortified;
	boolean memmove, memmoveFortified;
	
	FunctionMitigations()
	{
		libCXXHardenedABINot = new HashSet<String>();
		libCXXHardenedABI = new HashSet<String>();
	}
	
	public JsonObject toJSON(Function func) {
		JsonObject json = new JsonObject();
		
		json.addProperty("function", func.getName(true));
		
		json.addProperty("stackCanaryEnabled", stackCanaryEnabled);
		json.addProperty("stackCanaryBasicSupport", stackCanaryBasicSupport);
		json.addProperty("stackCanaryStrongSupport", stackCanaryStrongSupport);
		
		json.addProperty("libCXXHardenedEnabled", !libCXXHardenedABI.isEmpty());
		json.addProperty("libCXXHardenedSupported", (libCXXHardenedABI.size() + libCXXHardenedABINot.size()) > 0);
		json.addProperty("libCXXHardenedEnabledABI", libCXXHardenedABI.toString());
		json.addProperty("libCXXHardenedDisabledABI", libCXXHardenedABINot.toString());
		
		return json;
	}
	
	public String toString() {
		StringBuilder sb = new StringBuilder();
		
		sb.append("Stack Cannary [Enabled: ")
			.append(stackCanaryEnabled)
			.append("; Supported: ")
			.append(stackCanaryBasicSupport)
			.append("; Strong: ")
			.append(stackCanaryStrongSupport)
			.append("] ");
		
		sb.append("- LibCXX Hardening [Enabled: ")
			.append(libCXXHardenedABI.size())
			.append("; Disabled: ")
			.append(libCXXHardenedABINot.size())
			.append("; Supported: ")
			.append(libCXXHardenedABI.size() + libCXXHardenedABINot.size() > 0)
			.append("] ");
		
		return sb.toString();
	}
	
	// TODO: Finish this
	public void SetForFunction(SearchedFunction func) {
		switch(func)
		{
		case INVALID:
			return;
		case STACK_CHK_FAIL:
			this.stackCanaryEnabled = true;
			return;
		case MEMCPY:
			this.memcpy = true;
			return;
		case MEMCPY_FORTIFIED:
			this.memcpyFortified = true;
			return;
		}
	}
}


public class MitigationAnalysis extends GhidraScript {
	private Map<String, Boolean> libCXXHardeningVectors = new HashMap<>();
	
    public void run() throws Exception {
    	Gson gson = null;
		JsonWriter jsonWriter = null;
		Map<Function, FunctionMitigations> mitigations = null;
		
    	GhidraValuesMap values = new GhidraValuesMap();
		values.defineBoolean("Output To File", true);
		values.defineFile("Output File", File.createTempFile("mitigation-report-", "-" + currentProgram.getExecutableSHA256()));
		if (!SystemUtilities.isInHeadlessMode()) {
			values = this.askValues("Mitigation Analyzer", null, values);
		}
		
		File outputFile = values.getFile("Output File");
		if (SystemUtilities.isInHeadlessMode() || values.getBoolean("Output To File")) {
			gson = new GsonBuilder().setPrettyPrinting().create();
			jsonWriter = new JsonWriter(new FileWriter(outputFile));
			jsonWriter.beginArray();
		}
    	
    	FunctionManager manager = currentProgram.getFunctionManager();
    	GetLibCXXHardenedABI(manager);
    	
    	monitor.initialize(manager.getFunctionCount(), "Checking Mitigations");
    	
    	FunctionIterator funcIter = manager.getFunctions(true);
    	while (funcIter.hasNext() && !monitor.isCancelled()) {
    		Function func = funcIter.next();
    		monitor.increment();
    		
    		// Ignore CXX STL namespace functions from mitigation checks
    		String fullName = func.getName(true);
    		if (fullName.startsWith("std::") || fullName.startsWith("<EXTERNAL>::std::") || fullName.contains("::std::")) {
    			continue;
    		}
    		
        	// Check mitigations for function
    		FunctionMitigations funcMitigations = checkMitigations(func);
    		
    		if (jsonWriter != null && gson != null) {
				gson.toJson(funcMitigations.toJSON(func), jsonWriter);
    		} else {
    			println(fullName + " | " + funcMitigations.toString());
    		}
    	}
    	
    	if (jsonWriter != null) {
	    	jsonWriter.endArray();
			jsonWriter.close();
			println(outputFile.getAbsolutePath());
    	}
    }
    
    private void GetLibCXXHardenedABI(FunctionManager manager) {
    	FunctionIterator funcIter = manager.getFunctions(true);
    	
    	while (funcIter.hasNext() && !monitor.isCancelled()) {
    		Function func = funcIter.next();
    		
    		// Used for LibCXX Hardening Checks
    		String currentFuncName = func.getName(true);
        	if (!(currentFuncName.startsWith("std::vector<") && currentFuncName.contains(">::operator[][abi:"))) {
        		continue;
        	}
        	
			// We have a vector access, mark this function as accessing w/ this ABI
			int idx = currentFuncName.indexOf("[abi:");
			String abi = currentFuncName.substring(idx + 5, currentFuncName.length() - 1);
    		
    		// Check if function calls `size()` to validate access is within bounds
    		// If does then consider it "hardened"
    		for (Function calledFunc : func.getCalledFunctions(monitor)) {
    			if (calledFunc.getName().startsWith("size[")) {
    				libCXXHardeningVectors.put(abi, true);
    				return;
    			}
    		}
    		libCXXHardeningVectors.put(abi, false);
    	}	
    }

    private FunctionMitigations checkMitigations(Function func) {
    	FunctionMitigations mitigations = new FunctionMitigations();
    	
    	DecompInterface decompiler = new DecompInterface();
    	decompiler.openProgram(func.getProgram());
    	
    	DecompileResults results = decompiler.decompileFunction(func, 30, monitor);
    	if (!results.decompileCompleted()) {
    		return mitigations;
    	}
    	
    	HighFunction hf = results.getHighFunction();
    	Iterator<HighSymbol> symbols = hf.getLocalSymbolMap().getSymbols();
    	while (symbols.hasNext()) {
    		HighSymbol symbol = symbols.next();
    		if (symbol.getDataType() instanceof Array) {
				Array arr = (Array)symbol.getDataType();
				int elementSize = arr.getDataType().getLength();
				int numElements = arr.getNumElements();
				
				if (elementSize == 1 && numElements > 8) {
		    		// Base Stack Protector can be applied here
					mitigations.stackCanaryBasicSupport = true;
				}
				
				mitigations.stackCanaryStrongSupport = true;
    		}
    		
    		// TODO: Check if function has stack variable address taken
    	}
    	
    	for (Function calledFunc : func.getCalledFunctions(monitor)) {
    		String funcName = calledFunc.getName(true);
    		
    		SearchedFunction funcID = SearchedFunction.Find(funcName);
    		if (funcID != SearchedFunction.INVALID) {
    			mitigations.SetForFunction(funcID);
    			
    		} else if (funcName.startsWith("std::vector<") && funcName.contains(">::operator[][abi:")) {
    			// We have a vector access, mark this function as accessing w/ this ABI
    			int idx = funcName.indexOf("[abi:");
    			String abi = funcName.substring(idx + 5, funcName.length() - 1);
    			Boolean hardenedABI = libCXXHardeningVectors.get(abi);
    			if (hardenedABI == null || !hardenedABI) {
    				mitigations.libCXXHardenedABINot.add(abi);
    			} else {
    				mitigations.libCXXHardenedABI.add(abi);
    			}
    		}
    	}
    	
    	return mitigations;
    }
}
