package parser;

import java.security.interfaces.RSAMultiPrimePrivateCrtKey;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import org.antlr.v4.runtime.Token;

import parser.SimpleCParser.AddExprContext;
import parser.SimpleCParser.AssignStmtContext;
import parser.SimpleCParser.AssumeStmtContext;
import parser.SimpleCParser.AtomExprContext;
import parser.SimpleCParser.BandExprContext;
import parser.SimpleCParser.BlockStmtContext;
import parser.SimpleCParser.BorExprContext;
import parser.SimpleCParser.BxorExprContext;
import parser.SimpleCParser.CallStmtContext;
import parser.SimpleCParser.EqualityExprContext;
import parser.SimpleCParser.ExprContext;
import parser.SimpleCParser.FormalParamContext;
import parser.SimpleCParser.HavocStmtContext;
import parser.SimpleCParser.IfStmtContext;
import parser.SimpleCParser.LandExprContext;
import parser.SimpleCParser.LorExprContext;
import parser.SimpleCParser.MulExprContext;
import parser.SimpleCParser.NumberExprContext;
import parser.SimpleCParser.OldExprContext;
import parser.SimpleCParser.ParenExprContext;
import parser.SimpleCParser.ProcedureDeclContext;
import parser.SimpleCParser.RelExprContext;
import parser.SimpleCParser.ResultExprContext;
import parser.SimpleCParser.ShiftExprContext;
import parser.SimpleCParser.StmtContext;
import parser.SimpleCParser.TernExprContext;
import parser.SimpleCParser.UnaryExprContext;
import parser.SimpleCParser.VarDeclContext;
import parser.SimpleCParser.VarrefExprContext;

public class CallVisitor extends SimpleCBaseVisitor<String>{
	
	private Map<String, ArrayList<Integer>> variCount;
	private String assignedVar;
	private List<ExprContext> actuals;
	private Map<String, ExprContext> exParameterParameters = new HashMap<String,ExprContext>();
	private Map<String, ProcedureDeclContext> procedureContext = new HashMap<String, ProcedureDeclContext>();
	private ProcedureDeclContext thisProcedure;
	private List<VarDeclContext> globals = new ArrayList<VarDeclContext>();
	private List<String> globalVars = new ArrayList<String>();
	private Map<String, ArrayList<Integer>> oldVariCount;
	CallVisitor(){
		actuals = new ArrayList<ExprContext>();
	}

	public void getAllVar(Map<String, ArrayList<Integer>> variCount,String assignedVar,Map<String, ExprContext> exParameterParameters
			,ProcedureDeclContext thisProcedure, Map<String, ProcedureDeclContext> procedureContext, List<VarDeclContext> globals,Map<String, ArrayList<Integer>> oldVariCount){
		this.variCount = variCount;
		this.assignedVar = assignedVar;
		this.exParameterParameters = exParameterParameters;
		this.thisProcedure = thisProcedure;
		this.procedureContext = procedureContext;
		this.globals = globals;
		this.oldVariCount=oldVariCount;
	}
	public void getVarCount(Map<String, ArrayList<Integer>> variCount){
		this.variCount = variCount;
	}
	
//	@Override
//	public String visitCallStmt(CallStmtContext ctx) {
//			
//		String methodName = ctx.callee.getText();
//		
//		
//		if (procedureContext.containsKey(methodName)) {
//
//			this.thisProcedure = procedureContext.get(methodName);
//		}
//		
//		List<StmtContext> stmts = new ArrayList<StmtContext>();
//		stmts = thisProcedure.stmts;
//		
//		for (int i = 0; i < stmts.size(); i++) {
//			try {
//				String assignVar = stmts.get(i).assignStmt().lhs.getText();
//				for (VarDeclContext item : globals) {
//					if (item.name.getText().equals(assignVar) && !globalVars.contains(assignVar)) {
//						globalVars.add(assignVar);
//					}
//				}
//
//			} catch (NullPointerException e) {
//			}
//		}
//		
//		for (int i = 0; i < stmts.size(); i++) {
//			try {
//				this.visitCallStmt(stmts.get(i).callStmt());				
//			} catch (NullPointerException e) {
//			}
//		}
//
//		return "";
//		
//	}
	
	@Override
	public String visitVarrefExpr(VarrefExprContext ctx) {
		if(exParameterParameters.containsKey(ctx.getText())){
			ExprContext var = exParameterParameters.get(ctx.getText());
			return visitExpr(var);
		}else{
			return ctx.getText()+getSubscript(ctx.getText());
		}
		
	}
	
	@Override
	public String visitResultExpr(ResultExprContext ctx) {

//		String postVar = assignedVar;
//		postVar += getSubscript(postVar);
//		return postVar;
		
		String Expr = super.visitExpr(thisProcedure.returnExpr);
		return Expr;
	}
	
	@Override
	public String visitPrepost(SimpleCParser.PrepostContext ctx) {
		String result = super.visitPrepost(ctx);
		
		return result;
	}

	@Override
	public String visitRequires(SimpleCParser.RequiresContext ctx) {
		String requires;
		requires = this.visitExpr(ctx.condition);		
		return requires;
	}
	
	@Override
	public String visitEnsures(SimpleCParser.EnsuresContext ctx) {
	
		String ensures;
		ensures = this.visitExpr(ctx.condition);	
		return ensures;
	}

	
	//////////////////////////////////////////////////////////////////
	@Override
	public String visitExpr(ExprContext ctx) {
		String resSmt;
		resSmt = visitTernExpr(ctx.ternExpr());
		return resSmt;
	}

	@Override
	public String visitTernExpr(TernExprContext ctx) {
		StringBuilder resSmt = new StringBuilder("");
		LorExprContext single = ctx.single;
		String res;

		if (single != null) {
			resSmt.append(visitLorExpr(single));
		} else {
			resSmt.append("(ite  )");
			for (int i = 0; i < ctx.args.size(); i++) {
				LorExprContext temp;
				temp = ctx.args.get(i);

				res = visitLorExpr(temp);
				if ((i + 1) % 3 == 1) {
					res = isNotCondition(res);
					resSmt.insert(resSmt.length() - 3, " " + res);
				} else {
					res = isCondition(res);
					resSmt.insert(resSmt.length() - 1, " " + res);
				}

			}

			// ctx.getText());

		}
		return resSmt.toString();

	}

	@Override
	public String visitLorExpr(LorExprContext ctx) {
		StringBuilder resSmt = new StringBuilder("");
		LandExprContext single = ctx.single;
		String res;

		if (single != null) {

			resSmt.append(visitLandExpr(ctx.single));
		} else {
			Iterator<LandExprContext> iter = ctx.args.iterator();
			int i = 0;
			while (iter.hasNext()) {
				StringBuilder tempSmt = new StringBuilder("");
				LandExprContext temp;

				if (i < ctx.ops.size()) {
					tempSmt.append("(or )");
					i++;
				}

				temp = iter.next();
				res = super.visitLandExpr(temp);
				if (tempSmt.length() == 0) {
					res = isNotCondition(res);
					resSmt.insert(resSmt.length() - i, res);
				} else {
					res = isNotCondition(res);
					tempSmt.insert(tempSmt.length() - 1, res);
					resSmt.insert(resSmt.length() - i + 1, " " + tempSmt);
				}

			}
		}

		return resSmt.toString();

	}

	private String isNotCondition(String sub) {
		List<String> conOpList = new ArrayList<String>();
		conOpList.add("or");
		conOpList.add("an");
		conOpList.add("=");
		conOpList.add("no");
		conOpList.add("<");
		conOpList.add("<=");
		conOpList.add(">");
		conOpList.add(">=");
		// (> 1 1)
		if (!sub.contains("(")) {
			String result = "(itb " + sub + ")";
			return result;
		}
		if (sub.trim().length() > 3) {
			String op = sub.trim().substring(1, 3).trim();
			if (conOpList.contains(op)) {
				return sub;
			} else {
				String result = "(itb " + sub + ")";
				return result;
			}
		} else {
			String result = "(itb " + sub + ")";
			return result;
		}
	}

	@Override
	public String visitLandExpr(LandExprContext ctx) {
		StringBuilder resSmt = new StringBuilder("");
		BorExprContext single = ctx.single;
		String res;

		if (single != null) {
			resSmt.append(visitBorExpr(ctx.single));
		} else {
			Iterator<BorExprContext> iter = ctx.args.iterator();
			int i = 0;
			while (iter.hasNext()) {
				StringBuilder tempSmt = new StringBuilder("");
				BorExprContext temp;

				if (i < ctx.ops.size()) {
					tempSmt.append("(and )");
					i++;
				}

				temp = iter.next();

				res = visitBorExpr(temp);

				if (tempSmt.length() == 0) {
					res = isNotCondition(res);
					resSmt.insert(resSmt.length() - i, " " + res);
				} else {
					res = isNotCondition(res);
					tempSmt.insert(tempSmt.length() - 1, res);
					resSmt.insert(resSmt.length() - i + 1, " " + tempSmt);
				}

			}
		}

		return resSmt.toString();

	}

	@Override
	public String visitBorExpr(BorExprContext ctx) {
		StringBuilder resSmt = new StringBuilder("");
		BxorExprContext single = ctx.single;
		String res;

		if (single != null) {
			resSmt.append(visitBxorExpr(ctx.single));
		} else {
			Iterator<BxorExprContext> iter = ctx.args.iterator();
			int i = 0;
			while (iter.hasNext()) {
				StringBuilder tempSmt = new StringBuilder("");
				BxorExprContext temp;

				if (i < ctx.ops.size()) {
					tempSmt.append("(bv2int (bvor )");
					i++;
				}

				temp = iter.next();

				res = visitBxorExpr(temp);

				if (tempSmt.length() == 0) {
					resSmt.insert(resSmt.length() - i, " ((_ int2bv 32) " + res + "))");
				} else {
					tempSmt.insert(tempSmt.length() - 1, " ((_ int2bv 32) " + res + ")");
					resSmt.insert(resSmt.length() - i + 1, " " + tempSmt);
				}

			}
		}
		return resSmt.toString();
	}

	@Override
	public String visitBxorExpr(BxorExprContext ctx) {
		StringBuilder resSmt = new StringBuilder("");
		BandExprContext single = ctx.single;
		String res;

		if (single != null) {
			resSmt.append(visitBandExpr(ctx.single));
		} else {
			Iterator<BandExprContext> iter = ctx.args.iterator();
			int i = 0;
			while (iter.hasNext()) {
				StringBuilder tempSmt = new StringBuilder("");
				BandExprContext temp;

				if (i < ctx.ops.size()) {
					tempSmt.append("(bv2int (bvxor )");
					i++;
				}

				temp = iter.next();

				res = visitBandExpr(temp);

				if (tempSmt.length() == 0) {
					resSmt.insert(resSmt.length() - i, " ((_ int2bv 32) " + res + "))");
				} else {
					tempSmt.insert(tempSmt.length() - 1, "((_ int2bv 32) " + res + ")");
					resSmt.insert(resSmt.length() - i + 1, " " + tempSmt);
				}

			}
		}

		return resSmt.toString();

	}

	@Override
	public String visitBandExpr(BandExprContext ctx) {
		StringBuilder resSmt = new StringBuilder("");
		EqualityExprContext single = ctx.single;
		String res;

		if (single != null) {
			resSmt.append(visitEqualityExpr(ctx.single));
		} else {

			Iterator<EqualityExprContext> iter = ctx.args.iterator();
			int i = 0;
			while (iter.hasNext()) {
				StringBuilder tempSmt = new StringBuilder("");
				EqualityExprContext temp;

				if (i < ctx.ops.size()) {
					tempSmt.append("(bv2int (bvand )");
					i++;
				}

				temp = iter.next();
				res = visitEqualityExpr(temp);

				if (tempSmt.length() == 0) {
					resSmt.insert(resSmt.length() - i, " ((_ int2bv 32) " + res + "))");
				} else {
					tempSmt.insert(tempSmt.length() - 1, " ((_ int2bv 32) " + res + ")");
					resSmt.insert(resSmt.length() - i + 1, " " + tempSmt);
				}

			}
		}

		return resSmt.toString();

	}

	@Override
	public String visitEqualityExpr(EqualityExprContext ctx) {
		StringBuilder resSmt = new StringBuilder("");
		RelExprContext single = ctx.single;
		String res;

		if (single != null) {
			resSmt.append(visitRelExpr(ctx.single));

		} else {

			Iterator<RelExprContext> iter = ctx.args.iterator();
			int i = 0;
			String sign = "";
			int offset = 0;
			while (iter.hasNext()) {
				StringBuilder tempSmt = new StringBuilder("");
				RelExprContext temp;

				sign = i == ctx.ops.size() ? sign : ctx.ops.get(i).getText();
				if (i < ctx.ops.size()) {
					if (sign.equals("==")) {
						tempSmt.append("(= )");
						offset++;
					} else {
						tempSmt.append("(not (= ))");
						offset += 2;
					}
					i++;
				}

				temp = iter.next();

				res = visitRelExpr(temp);

				if (tempSmt.length() == 0) {
					resSmt.insert(resSmt.length() - offset, " " + res);
				} else {
					if (sign.equals("==")) {
						res = isCondition(res);
						tempSmt.insert(tempSmt.length() - 1, res);
						resSmt.insert(resSmt.length() - i + 1, " " + tempSmt);
					} else {
						res = isCondition(res);
						tempSmt.insert(tempSmt.length() - 2, res);
						resSmt.insert(resSmt.length() - i + 1, " " + tempSmt);
					}

				}

			}
		}

		return resSmt.toString();
	}

	@Override
	public String visitRelExpr(RelExprContext ctx) {
		StringBuilder resSmt = new StringBuilder("");
		ShiftExprContext single = ctx.single;
		String res;

		if (single != null) {
			resSmt.append(visitShiftExpr(ctx.single));
		} else {
			
			Iterator<ShiftExprContext> iter = ctx.args.iterator();
			int i = 0;
			while (iter.hasNext()) {
				StringBuilder tempSmt = new StringBuilder("");
				ShiftExprContext temp;

				if (i < ctx.ops.size()) {
					tempSmt.append("(" + ctx.ops.get(i).getText() + " )");
					i++;
				}

				temp = iter.next();
				res = visitShiftExpr(temp);

				if (tempSmt.length() == 0) {
					res = isCondition(res);
					resSmt.insert(resSmt.length() - i, " " + res);
				} else {
					res = isCondition(res);
					tempSmt.insert(tempSmt.length() - 1, res);
					resSmt.insert(resSmt.length() - i + 1, " " + tempSmt);
				}

			}
		}
		return resSmt.toString();

	}

	@Override
	public String visitShiftExpr(ShiftExprContext ctx) {
		StringBuilder resSmt = new StringBuilder("");
		AddExprContext single = ctx.single;
		String res;

		if (single != null) {
			resSmt.append(visitAddExpr(ctx.single));
		} else {
			Iterator<AddExprContext> iter = ctx.args.iterator();
			int i = 0;
			while (iter.hasNext()) {
				StringBuilder tempSmt = new StringBuilder("");
				AddExprContext temp;

				if (i < ctx.ops.size()) {
					if (ctx.ops.get(i).getText().equals("<<")) {
						tempSmt.append("(bv2int (bvshl )");
					} else {
						tempSmt.append("(bv2int (bvashr )");
					}

					i++;
				}

				temp = iter.next();

				res = visitAddExpr(temp);

				if (tempSmt.length() == 0) {
					resSmt.insert(resSmt.length() - i, " ((_ int2bv 32) " + res + "))");
				} else {
					tempSmt.insert(tempSmt.length() - 1, " ((_ int2bv 32) " + res + ")");
					resSmt.insert(resSmt.length() - i + 1, " " + tempSmt);
				}

			}
		}

		return resSmt.toString();
	}

	@Override
	public String visitNumberExpr(NumberExprContext ctx) {
		return ctx.getText();
	}

	@Override
	public String visitParenExpr(ParenExprContext ctx) {
		String res = super.visitExpr(ctx.arg);
		return res;
	}

	@Override
	public String visitAddExpr(AddExprContext ctx) {
		/*
		 */
		StringBuilder result = new StringBuilder();
		List<String> opsList = new ArrayList<String>();
		for (Token token : ctx.ops) {
			opsList.add(token.getText());
		}
		// Get the arg from super
		if (opsList.isEmpty()) {
			return this.visitMulExpr((MulExprContext) ctx.getChild(0));
		} else {
			String sub;
			for (int i = 0; i < opsList.size(); i++) {
				sub = this.visitMulExpr(ctx.args.get(i));
				sub = isCondition(sub);
				result.append("(" + opsList.get(i) + " " + sub);
			}
			sub = this.visitMulExpr(ctx.args.get(ctx.args.size() - 1));
			sub = isCondition(sub);
			result.append(" " + sub);
			for (int i = 0; i < opsList.size(); i++) {
				result.append(")");
			}
		}
		return result.toString();
	}

	private String isCondition(String sub) {
		List<String> conOpList = new ArrayList<String>();
		conOpList.add("or");
		conOpList.add("an");
		conOpList.add("=");
		conOpList.add("no");
		conOpList.add("<");
		conOpList.add("<=");
		conOpList.add(">");
		conOpList.add(">=");
		// (> 1 1)
		if (sub.trim().length() > 3) {
			String op = sub.trim().substring(1, 3).trim();
			if (conOpList.contains(op)) {
				String result = "(bti " + sub + ")";
				return result;
			} else {
				return sub;
			}
		} else {
			return sub;
		}
	}

	@Override
	public String visitMulExpr(MulExprContext ctx) {
		StringBuilder result = new StringBuilder();
		List<String> opsList = new ArrayList<String>();
		for (Token token : ctx.ops) {
			opsList.add(token.getText());
		}
		// Get the arg from super
		if (opsList.isEmpty()) {
			return this.visitUnaryExpr((UnaryExprContext) ctx.getChild(0));
		} else {
			for (int i = 0; i < opsList.size(); i++) {
				String operator = opsList.get(i);
				if (operator.equals("%")) {
					operator = "mymod";
				}
				if (operator.equals("/")) {
					operator = "mydiv";
				}
				result.append("(" + operator + " " + this.visitUnaryExpr(ctx.args.get(i)));
			}
			result.append(" " + this.visitUnaryExpr(ctx.args.get(ctx.args.size() - 1)));
			for (int i = 0; i < opsList.size(); i++) {
				result.append(")");
			}
		}
		return result.toString();
	}

	@Override
	public String visitUnaryExpr(UnaryExprContext ctx) {
		StringBuilder result = new StringBuilder();
		List<String> opsList = new ArrayList<String>();
		for (Token token : ctx.ops) {
			opsList.add(token.getText());
		}
		if (opsList.isEmpty()) {
			return this.visitAtomExpr((AtomExprContext) ctx.getChild(0));
		} else {
			for (int i = 0; i < opsList.size(); i++) {
				result.append("(" + opsList.get(i) + " ");
			}
			result.append(" " + this.visitAtomExpr(ctx.arg));
			for (int i = 0; i < opsList.size(); i++) {
				result.append(")");
			}
		}
		return result.toString();
	}

	@Override
	public String visitAtomExpr(AtomExprContext ctx) {
		return super.visitAtomExpr(ctx);
	}

	@Override
	public String visitHavocStmt(HavocStmtContext ctx) {
		incSubscript(ctx.getChild(1).getText());
		return super.visitHavocStmt(ctx);
	}

	@Override
	public String visitOldExpr(OldExprContext ctx) {
		String varible = ctx.getChild(2).getText();
		String oldResult = varible + this.getGlobaOldSubscript(varible);
		return oldResult;
	}
	
	private int getGlobaOldSubscript(String varible) {
		return this.oldVariCount.get(varible).get(1);
	}
	
	/** Get current subscripte for a specific variable **/
	private String getSubscript(String text) {
		if(variCount.containsKey(text))
			return variCount.get(text).get(1).toString();
		else
			return  "";
	}

	/** Increase the subscript while assigned **/
	private void incSubscript(String text) {
		// TODO : Declaration
		variCount.get(text).set(1, Integer.getInteger(getSubscript(text)) + 1);
	}

	/** Remove all local variables, later use **/
	@SuppressWarnings("unused")
	private void rmLocalVar() {
		for (Map.Entry<String, ArrayList<Integer>> iter : this.variCount.entrySet()) {
			if (iter.getValue().get(0) == 1) {
				this.variCount.remove(iter.getKey());
			}
		}
	}

}
