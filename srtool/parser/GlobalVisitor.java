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
	
	public Void visitCallStmt(CallStmtContext ctx) {
		inProcedure = 1;
		super.visitCallStmt(ctx);
		inProcedure = 0;
		return null;
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
	public String getSMT() {
		return ResSmt.toString();
	}
	
	
}
