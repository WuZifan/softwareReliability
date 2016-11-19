package parser;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;



public class VariCount {
	/*
	 * varCount stores all the variables 
	 * the first element indicates whether it is global or local:
	 * 0:global       1: local
	 * the second one counts the times 
	 * start with 0
	 * the third element indicates the initial index when entering the procedure
	 * the fourth element indicates the current index of available number
	 * the fifth element stores the initial index before enter the if-else
	 * */
	private Map<String, ArrayList<Integer> > varCount = new HashMap<String, ArrayList<Integer> >();
	
	/*
	 * IfLayer stores information about if condition structure
	 * Key is the layer of the if condition
	 * HashMap keys store the condition of this layer in SMT form, values means it is in if or else
	 * 1: if          0: else
	 */
	private HashMap<Integer, HashMap<String, Integer >> ifLayer = new HashMap<Integer, HashMap<String, Integer>>();
	
	public Map<String, ArrayList<Integer> > getVarCount() {
		return varCount;
	}

	public void setVarCount(Map<String, ArrayList<Integer> > varCount) {
		this.varCount = varCount;

	}
	
	public HashMap<Integer, HashMap<String, Integer >> getIfLayer() {
		return this.ifLayer;
	}

	
	
	
}
