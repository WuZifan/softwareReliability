package parser;

import java.util.ArrayList;
import java.util.List;

import parser.SimpleCParser.AssertStmtContext;

public class MyAssertVisitor extends SimpleCBaseVisitor<Void> {
	private StringBuilder nomorAss = new StringBuilder();
	private StringBuilder unnomAss = new StringBuilder();
	private boolean unnomFlag = false;
	public List<String> unnoList = new ArrayList<String>();

	public MyAssertVisitor() {
	}

	@Override
	public Void visitAssertStmt(AssertStmtContext ctx) {
		unnomFlag = true;
		return super.visitAssertStmt(ctx);
	}

	public Void visitunnomAss(String text) {
		unnomFlag = true;
		unnomAss.append(text);
		unnoList.add(text);
		System.out.println("myassert: "+text);
		return null;
	}

	public Void visitnomorAss(String text) {
		nomorAss.append(text);
		return null;
	}

	public String getUnAssSMT() {
		if (!unnoList.isEmpty()) {
			// return "(and "+unnomAss.append(" )").toString();
			String unnomRe=unnoList.get(0);
			for(int i=1;i<unnoList.size();i++){
				unnomRe="(and "+unnoList.get(i)+" "+unnomRe+")";
			}
			return unnomRe;
		} else {
			return "";
		}
	}

	public String getAssSMT() {

		return nomorAss.toString();
	}
}
