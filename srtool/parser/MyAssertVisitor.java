package parser;

import parser.SimpleCParser.AssertStmtContext;

public class MyAssertVisitor extends SimpleCBaseVisitor<Void> {
	private StringBuilder nomorAss=new StringBuilder();
	private StringBuilder unnomAss=new StringBuilder();
	private boolean unnomFlag=false;
	
	public MyAssertVisitor() {
		unnomAss.append("(assert (not (and");
	}
	/**
	 * 回去修改下Assert
	 */
	@Override
	public Void visitAssertStmt(AssertStmtContext ctx) {
		unnomFlag=true;
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
		unnomFlag=true;
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
		if(unnomFlag){
		unnomAss.append(")))\n");
		return nomorAss.toString()+unnomAss.toString();
		}else{
			return nomorAss.toString();
		}
	}
	
	public String getUnAssSMT(){
		return unnomAss.append(")))\n").toString();
	}
}
