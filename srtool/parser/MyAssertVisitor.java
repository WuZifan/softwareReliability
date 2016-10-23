package parser;

import parser.SimpleCParser.AssertStmtContext;

public class MyAssertVisitor extends SimpleCBaseVisitor<Void> {
	private StringBuilder nomorAss=new StringBuilder();
	private StringBuilder unnomAss=new StringBuilder();
	
	public MyAssertVisitor() {
		unnomAss.append("(assert (not (and");
	}
	
	@Override
	public Void visitAssertStmt(AssertStmtContext ctx) {
		
		return super.visitAssertStmt(ctx);
	}
	
	/**
	 * 传入这样的参数：
	 * 	(assert (not (and(<= i0 4294967295)(>= i0 0)(<= i1 4294967295)(>= i1 0))))
	 * 	text="(>= i0 0)"
	 * @param text
	 * @return
	 */
	public Void visitunnomAss(String text){
		unnomAss.append(text);
		return null;
	}
	/**
	 * 传入这样的参数：
	 * 	text="(assert (= i0 4294967298))"
	 * @param text
	 * @return
	 */
	public Void visitnomorAss(String text){
		nomorAss.append(text);
		return null;
	}
	
	public String getAssSMT(){
		unnomAss.append(")))\n");
		return nomorAss.toString()+unnomAss.toString();
	}
}
