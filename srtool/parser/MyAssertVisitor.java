package parser;

import parser.SimpleCParser.AssertStmtContext;

public class MyAssertVisitor extends SimpleCBaseVisitor<Void> {
	private StringBuilder nomorAss=new StringBuilder();
	private StringBuilder unnomAss=new StringBuilder();
	private boolean unnomFlag=false;
	
	public MyAssertVisitor() {
		//unnomAss.append("(and ");
	}
	/**
	 */
	@Override
	public Void visitAssertStmt(AssertStmtContext ctx) {
		unnomFlag=true;
		return super.visitAssertStmt(ctx);
	}
	
	/**
	 * 	(assert (not (and(<= i0 4294967295)(>= i0 0)(<= i1 4294967295)(>= i1 0))))
	 * 	text="(>= i0 0)"
	 * @param text
	 * @return
	 */
	public Void visitunnomAss(String text){
		unnomFlag=true;
		unnomAss.append(text);
		return null;
	}
	/**
	 * 	text="(assert (= i0 4294967298))"
	 * @param text
	 * @return
	 */
	public Void visitnomorAss(String text){
		nomorAss.append(text);
		return null;
	}
	
	public String getAssSMT(){
	
		return nomorAss.toString();
	}
	
	public String getUnAssSMT(){
		if(!unnomAss.toString().isEmpty())
			return "(and "+unnomAss.append(" )").toString();
		
		else
			return "";
	}
}
