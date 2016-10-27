package parser;

import parser.SimpleCParser.*;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class GlobalVisitor extends SimpleCBaseVisitor<Void> {
	private int inProcedure;
	private StringBuilder ResSmt;
	private Map<String, ArrayList<Integer> > variCount;

	
	public GlobalVisitor(VariCount variCount) {
		this.inProcedure = 0;
		this.ResSmt = new StringBuilder("");
		this.variCount = variCount.getVarCount();
	}
	
	/** Current: global variable checking **/
	public Void visitCallStmt(CallStmtContext ctx) {
		/** Assign status code to 1 while in procedure statement **/
		this.inProcedure = 1;
		super.visitCallStmt(ctx);
		this.inProcedure = 0;
		return null;
	}
	
	/** Current: global variable checking **/
	public Void visitProcedureDecl(ProcedureDeclContext ctx) {
		/** Assign status code to 1 while in procedure statement **/
		this.inProcedure = 1;
		super.visitProcedureDecl(ctx);
		this.inProcedure = 0;
		return null;
	}
	
	/** Only get declaration of global variable, assignment will in procedure **/
	public Void visitVarDecl(VarDeclContext ctx) {
		/** Not in procedure will end immediately **/
		if(this.inProcedure == 1) {
			return null;
		}
		
		ArrayList<Integer> status = new ArrayList<Integer>();
		status.add(0);
		status.add(0);
		String variName = ctx.getChild(1).getText();
		this.variCount.put(variName, status);
		variName = variName + "0";
		this.ResSmt.append(getDeclStmt(variName).toString());
		System.out.println(this.ResSmt.toString());
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
		// for int
		result.append(typeName + ")");
		// for reals
//		result.append("Real"+")");
		result.append("\n");
		return result.toString();
	}
	
	public String getSMT() {
		return ResSmt.toString();
	}
	
	
}
