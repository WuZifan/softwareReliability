package parser;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;



public class VariCount {
	/*
	 * varCount stores all the varibles 
	 * the first element shows whether it is global or local:
	 * 0:global       1: local
	 * the second one counts the times 
	 * start with 0
	 * */
	private Map<String, ArrayList<Integer> > varCount = new HashMap<String, ArrayList<Integer> >();
	private ArrayList<Integer> ifLayer = new ArrayList<Integer>();
	
	public Map<String, ArrayList<Integer> > getVarCount() {
		return varCount;
	}

	public void setVarCount(Map<String, ArrayList<Integer> > varCount) {
		this.varCount = varCount;

	}
	
	public ArrayList<Integer> getIfLayer() {
		return this.ifLayer;
	}

	
	
	
}
