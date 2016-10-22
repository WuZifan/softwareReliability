package parser;

import java.util.ArrayList;
import java.util.List;

import parser.SimpleCParser.AssignStmtContext;
import parser.SimpleCParser.VarDeclContext;
import parser.SimpleCParser.VarrefExprContext;

public class TestVisitor extends SimpleCBaseVisitor<Void> {
	private static List<String> idList = new ArrayList<String>();
	private StringBuilder  smtResult=new StringBuilder();
	@Override
	public Void visitVarDecl(VarDeclContext ctx) {
		StringBuilder testSMT = new StringBuilder();
		// TODO Auto-generated method stub
//		System.out.println(ctx.getChildCount());
//		System.out.println(ctx.getChild(0).getText());
		String typeName = ctx.getChild(0).getText();
		String variName = ctx.getChild(1).getText();
		
		if (!idList.contains(variName)) {
			idList.add(variName);
			
			testSMT.append("(declare-fun ");
			testSMT.append(variName+" ");
			testSMT.append("() ");
			if(typeName.equals("int")){
				typeName="Int";
			}
			testSMT.append(typeName + ")");
			testSMT.append("\n");
			testSMT.append("(assert true)\n");
		} else {
			testSMT.append("(assert false)");
		}
		
		super.visitVarDecl(ctx);
		smtResult.append(testSMT.toString());
		// return super.visitVarDecl(ctx);
		return null;
	}

	@Override
	public Void visitAssignStmt(AssignStmtContext ctx) {
		StringBuilder result=new StringBuilder();
		String variName=ctx.getChild(0).getText();
		String num=ctx.getChild(2).getText();
//		long num=Long.parseLong(num);
		if(idList.contains(variName)){
			// i=1;
			result.append("(assert (= ");
			result.append (variName+" ");
			result.append(num);
			result.append("))");
			result.append("\n");
			result.append("(assert (not (and (<= ");
			result.append(variName);
			result.append(" 4294967295) (>= ");
			result.append(variName);
			result.append(" 0))))");
			result.append("\n");
		}else{
			result.append("(assert true)");
		}
		smtResult.append(result.toString());
		return super.visitAssignStmt(ctx);
	}	
	
	public String getSMT() {
		return smtResult.toString();
	}
}
