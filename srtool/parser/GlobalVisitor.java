package parser;

import parser.SimpleCParser.*;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class GlobalVisitor extends SimpleCBaseVisitor {
	private int inProcedure = 0;
	private StringBuilder ResSmt = new StringBuilder("");
	private static Map<String, Integer> variCount = new HashMap<String, Integer>();
	private MyAssertVisitor assVisitor;
	
	public GlobalVisitor(MyAssertVisitor assVisitor){
		this.assVisitor=assVisitor;
	}
	
	public GlobalVisitor() {
		
	}
	
	public Void visitCallStmt(CallStmtContext ctx) {
		inProcedure = 1;
		super.visitCallStmt(ctx);
		inProcedure = 0;
		return null;
	}
	
	public Void visitProcedureDecl(ProcedureDeclContext ctx) {
		inProcedure = 1;
		super.visitProcedureDecl(ctx);
		inProcedure = 0;
		return null;
	}
	
	public Void visitVarDecl(VarDeclContext ctx) {
		if(inProcedure == 1) {
			return null;
		}
		String variName = ctx.getChild(1).getText();
	
		variCount.put(variName, 0);
		variName = variName + "0";
		ResSmt.append(getDeclStmt(variName).toString());
		
		return null;
		
	}
	
	@Override
	public Void visitAssignStmt(AssignStmtContext ctx) {
		// 被赋值的变量名，且取下标
		String variName = getSubscript(ctx.getChild(0).getText());
		
		// 暂时只考虑单个数字赋值
		String num = ctx.getChild(2).getText();
		
		// not类型的assert.
		StringBuilder unnomAss=new StringBuilder();
		
		// 普通类型的asert
		StringBuilder nomoAss=new StringBuilder();
		// 赋值语句
		nomoAss.append("(assert (= "+variName+" "+num+"))\n");
		assVisitor.visitnomorAss(nomoAss.toString());
		
		// 判断是否超过限制
		unnomAss.append("(<= "+variName+" 4294967295)");
		unnomAss.append("(>= "+variName+" 0)");
		assVisitor.visitunnomAss(unnomAss.toString());

		// 只是定义超限报错，但是具体行为没有报错

		// 下标问题
		super.visitAssignStmt(ctx);
		return null;
	}
	
	private String getSubscript(String text) {
		// 获得下标
		int subScript = variCount.get(text);
		// 下标更新
		int nextSubscript = subScript+1;
		// 重新声明新的变量,变量名+新下标
		String newDecl="";
		if(subScript!=0){
			newDecl=getDeclStmt(text+subScript);
		}else{
			variCount.put(text, new Integer(nextSubscript));
			return text+"0";
		}
		// 把变量名+新下标重新塞入Map
		variCount.put(text, new Integer(nextSubscript));
		// 添加到整段SMT语句中
		ResSmt.append(newDecl);
		// 返回变量名+原下标
		return text + subScript;
	}
	
	// 获取声明语句的SMT语句
	private String getDeclStmt(String variName) {
		StringBuilder result = new StringBuilder();
		String typeName="Int";
		// 编写SMT语句
		result.append("(declare-fun ");
		result.append(variName + " ");
		result.append("() ");
		result.append(typeName + ")");
		result.append("\n");
		return result.toString();
	}
	
	public String getSMT() {
		return ResSmt.toString();
	}
	
	
}
