package parser;

import parser.SimpleCParser.*;
import java.util.ArrayList;
import java.util.List;

public class GlobalVisitor extends SimpleCBaseVisitor {
	private int inProcedure = 0;
	private StringBuilder ResSmt = new StringBuilder("");
	private static List<String> idList = new ArrayList<String>();
	
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
		System.out.println("not in procedure");
		String typeName = ctx.getChild(0).getText();
		String variName = ctx.getChild(1).getText();
		
		if (!idList.contains(variName)) {
			idList.add(variName);
			
			ResSmt.append("(declare-fun ");
			ResSmt.append(variName+" ");
			ResSmt.append("() ");
			if(typeName.equals("int")){
				typeName="Int";
			}
			ResSmt.append(typeName + ")");
			ResSmt.append("\n");
			ResSmt.append("(assert false)\n");
		} else {
			ResSmt.append("(assert true)");
		}
		return null;
		
	}
	public String getSMT() {
		return ResSmt.toString();
	}
	
}
