package parser;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import org.antlr.v4.runtime.Token;

import parser.SimpleCParser.*;
import parser.SimpleCParser.AddExprContext;
import parser.SimpleCParser.AssignStmtContext;
import parser.SimpleCParser.BandExprContext;
import parser.SimpleCParser.BorExprContext;
import parser.SimpleCParser.BxorExprContext;
import parser.SimpleCParser.EqualityExprContext;
import parser.SimpleCParser.ExprContext;
import parser.SimpleCParser.IfStmtContext;
import parser.SimpleCParser.LandExprContext;
import parser.SimpleCParser.LorExprContext;
import parser.SimpleCParser.NumberExprContext;
import parser.SimpleCParser.ParenExprContext;
import parser.SimpleCParser.RelExprContext;
import parser.SimpleCParser.ShiftExprContext;
import parser.SimpleCParser.TernExprContext;
import parser.SimpleCParser.UnaryExprContext;
import parser.SimpleCParser.VarDeclContext;
import parser.SimpleCParser.VarrefExprContext;

public class TestVisitor extends SimpleCBaseVisitor<String> {
	private Map<String, ArrayList<Integer>> variCount;
	private StringBuilder smtResult;
	private MyAssertVisitor assVisitor;
	private HashMap<Integer, HashMap<String, Integer >> ifLayer;
	


	public TestVisitor() {
		this.smtResult = new StringBuilder();
	}

	public TestVisitor(MyAssertVisitor assVisitor, VariCount variCount, String glSmt, String plSmt) {
		this.assVisitor = assVisitor;
		this.variCount = variCount.getVarCount();
		this.ifLayer = variCount.getIfLayer();
		this.smtResult = new StringBuilder();
//		this.smtResult.append(glSmt);
//		this.smtResult.append(plSmt);

	}

	public TestVisitor(MyAssertVisitor assVisitor, VariCount variCount) {
		this.assVisitor = assVisitor;
		this.variCount = variCount.getVarCount();
		this.ifLayer = variCount.getIfLayer();
		this.smtResult = new StringBuilder();
	}

	@Override
	public String visitAssertStmt(AssertStmtContext ctx) {
		String text = this.visitExpr(ctx.expr());
		System.out.println("assert:++++++++" + text);
		if(!text.contains("(")){
			text=isNotCondition(text);
		}
		this.assVisitor.visitunnomAss(text);
		return null;
	}
	
	@Override
	public String visitAssumeStmt(AssumeStmtContext ctx) {
		
		String text = this.visitExpr(ctx.expr());
		text = ("(assert " +text+ ")\n");
		this.smtResult.append(text);
		return null;
	}

	@Override
	public String visitVarDecl(VarDeclContext ctx) {
		StringBuilder result = new StringBuilder();
		String variName = ctx.getChild(1).getText();
		ArrayList<Integer> status = new ArrayList<Integer>();
		status.add(1);
		status.add(0);
		variCount.put(variName, status);
		variName = variName + "0";
//		result.append(getDeclStmt(variName));
		super.visitVarDecl(ctx);
		return null;
	}

	@Override
	public String visitAssignStmt(AssignStmtContext ctx) {
		System.out.println("**\nAssign: "+ctx.getText());
		// String num = ctx.getChild(2).getText();
		String num = this.visitExpr((ExprContext) ctx.getChild(2));

		//incSubscript(name);
		String name = ctx.getChild(0).getText();
		incSubscript(name);
		String variName = name + getSubscript(name);
		StringBuilder unnomAss = new StringBuilder();

		StringBuilder nomoAss = new StringBuilder();
		num=isCondition(num);
		nomoAss.append("(assert (= " + variName + " " + num + "))\n");
		//assVisitor.visitnomorAss(nomoAss.toString());
		this.smtResult.append(nomoAss.toString());

		unnomAss.append("(<= " + variName + " 4294967295)");
		unnomAss.append("(>= " + variName + " 0)");
		//assVisitor.visitunnomAss(unnomAss.toString());
		return nomoAss.toString();
	}
	
	@Override
	public String visitIfStmt(IfStmtContext ctx) {
		Map<String, ArrayList<Integer>> init = new HashMap<String, ArrayList<Integer>>();
		Map<String, ArrayList<Integer>> afif = new HashMap<String, ArrayList<Integer>>();
		StringBuilder resSmt = new StringBuilder("");
		HashMap<String, Integer> iftemp;
		int layer;
		String cond, strif, strelse;
		
		/** store initial info of variable **/
		init = copyMap(this.variCount);
		
		/** receive condition SMT **/
		cond = super.visitExpr(ctx.condition);
		
		/** prepare if information **/
		layer = this.ifLayer.size();
		iftemp = new HashMap<String, Integer>();
		iftemp.put(cond, 1);
		this.ifLayer.put(layer + 1, iftemp);

		/** visit if bloc statement **/
		strif = visitBlockStmt(ctx.thenBlock);
//		smtResult.append(strif);
		
		/** store variable info after if **/
		afif = copyMap(this.variCount);

		/** detect else statement then enter **/
		if(ctx.elseBlock != null) {
			this.ifLayer.get(layer + 1).put(cond, 0);
			strelse = visitBlockStmt(ctx.elseBlock);
//			smtResult.append(strelse);

			/** Compare differences and generate Smt for if **/
			for(String key : afif.keySet()) {

				String tempSmt = "";
				if(afif.get(key).get(1) > this.variCount.get(key).get(1)) {
					tempSmt += "(assert (= " + key + (Integer.toString(afif.get(key).get(1)+1));
					tempSmt += " (ite " + cond + " " + key + Integer.toString(afif.get(key).get(1) );
					tempSmt += " " + key + Integer.toString(this.variCount.get(key).get(1) ) + "))\n";
					incSubscript(key);
				}
				else if(afif.get(key).get(1) < this.variCount.get(key).get(1)) {
					tempSmt += "(assert (= " + key + (Integer.toString(this.variCount.get(key).get(1)+1));
					tempSmt += " (ite " + cond + " " + key + Integer.toString(this.variCount.get(key).get(1) );
					tempSmt += " " + key + Integer.toString(afif.get(key).get(1) ) + ")))\n";
					incSubscript(key);
				}
				else if(afif.get(key).get(1) > init.get(key).get(1)) {
					tempSmt += "(assert (= " + key + (Integer.toString(this.variCount.get(key).get(1)+1));
					tempSmt += " (ite " + cond + " " + key + Integer.toString(afif.get(key).get(1) );
					tempSmt += " " + key + Integer.toString((init.get(key).get(1)) ) + ")))\n";
					incSubscript(key);
				}
				resSmt.append(tempSmt);
			}
		}
		
		this.ifLayer.remove(layer + 1);


	//	System.out.println("if res : " + resSmt.toString());
		smtResult.append(resSmt);
		return resSmt.toString();
	}

	@Override
	public String visitBlockStmt(BlockStmtContext ctx) {
		StringBuilder res = new StringBuilder();
		
		for(StmtContext iter : ctx.stmts) {
			res.append(visitStmt(iter));
		}
		
		return res.toString();
	}
	
	@Override
	public String visitExpr(ExprContext ctx) {
		String resSmt;
		resSmt = visitTernExpr(ctx.ternExpr());
		System.out.println("-----");
		 System.out.println("expr is " + resSmt);
		 System.out.println(ctx.getText());
		return resSmt;
	}

	@Override
	public String visitTernExpr(TernExprContext ctx) {
		StringBuilder resSmt = new StringBuilder("");
		LorExprContext single = ctx.single;
		String res;

		if (single != null) {
			// System.out.println(single.getText());
			resSmt.append(visitLorExpr(single));
		} else {
			resSmt.append("(ite  )");
			for(int i = 0; i < ctx.args.size(); i++) {
				LorExprContext temp;
				temp = ctx.args.get(i);

//				System.out.println("dealing " + temp.getText());
				res = visitLorExpr(temp);
//				System.out.println("res " + res + "   " + ctx.getText());
				if ((i + 1) % 3 == 1) {
					System.out.println(res);
					res=isNotCondition(res);
					resSmt.insert(resSmt.length() - 3, " " + res);
				}
				else {
					res=isCondition(res);
					resSmt.insert(resSmt.length() - 1, " " + res);
				}
				

			}

	//		System.out.println("answer " + resSmt.toString() + " " + ctx.getText());

		}
		System.out.println(resSmt.toString());
		System.out.println();
		return resSmt.toString();

	}

	@Override
	public String visitLorExpr(LorExprContext ctx) {
		StringBuilder resSmt = new StringBuilder("");
		LandExprContext single = ctx.single;
		String res;

		if (single != null) {

			resSmt.append(visitLandExpr(ctx.single));
		}
		else {
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
				// System.out.println("dealing " + temp.getText());
				res = super.visitLandExpr(temp);
				if (tempSmt.length() == 0) {
					res=isNotCondition(res);
					resSmt.insert(resSmt.length() - i,  res );
				} else {
					res=isNotCondition(res);
					tempSmt.insert(tempSmt.length() - 1, res );
					resSmt.insert(resSmt.length() - i + 1, " " + tempSmt);
				}

			}
		}
		
	//	System.out.println("fde" + resSmt.toString());
		return resSmt.toString();

	}

	private String isNotCondition(String sub) {
		List<String> conOpList=new ArrayList<String>();
		conOpList.add("or");conOpList.add("an");conOpList.add("=");conOpList.add("no");
		conOpList.add("<");conOpList.add("<=");conOpList.add(">");conOpList.add(">=");
		// (> 1 1)
		if(!sub.contains("(")){
			String result="(itb "+sub+")";
			return result;
		}
		if(sub.trim().length()>3){
			String op=sub.trim().substring(1, 3).trim();
			if(conOpList.contains(op)){
				return sub;
			}else{
				String result="(itb "+sub+")";
				return result;
			}
		}else{
			String result="(itb "+sub+")";
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
		}
		else {
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

//				System.out.println("dealing " + temp.getText());
				res = visitBorExpr(temp);

				if (tempSmt.length() == 0) {
					res=isNotCondition(res);
					resSmt.insert(resSmt.length() - i, " " + res);
				} else {
					res=isNotCondition(res);
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
		}
		else {
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

		//		System.out.println("dealing " + temp.getText());
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
		}
		else {
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

			//	System.out.println("dealing " + temp.getText());
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
		}
		else {

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
			//	System.out.println("dealing " + temp.getText());
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

		}
		else {

			Iterator<RelExprContext> iter = ctx.args.iterator();
			int i = 0;
			String sign = "";
			int offset = 0;
			while (iter.hasNext()) {
				StringBuilder tempSmt = new StringBuilder("");
				RelExprContext temp;
				
				sign = i == ctx.ops.size() ? sign : ctx.ops.get(i).getText();
		//		System.out.println("sign: " + sign);
				if (i < ctx.ops.size()) {
					if (sign.equals("==")) {
				//		System.out.println("enter");
						tempSmt.append("(= )");
						offset ++;
					}
					else {
						tempSmt.append("(not (= ))");
						offset += 2;
					}			
					i++;
				}
				
			
				temp = iter.next();

//				System.out.println("dealing " + temp.getText());
				res = visitRelExpr(temp);

				if (tempSmt.length() == 0) {
					resSmt.insert(resSmt.length() - offset, " " + res);
				} else {
					if (sign.equals("==")) {
						res=isCondition(res);
						tempSmt.insert(tempSmt.length() - 1, res);
						resSmt.insert(resSmt.length() - i + 1, " " + tempSmt);
					}
					else {
						res=isCondition(res);
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
		}
		else {
			// （> (>1 2) 2）
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
		//		System.out.println("dealing " + temp.getText());
				res = visitShiftExpr(temp);

				if (tempSmt.length() == 0) {
					res=isCondition(res);
					resSmt.insert(resSmt.length() - i, " " + res);
				} else {
					res=isCondition(res);
					tempSmt.insert(tempSmt.length() - 1, res);
					resSmt.insert(resSmt.length() - i + 1, " " + tempSmt);
				}

			}
		}
//		System.out.println("IfSMT： "+resSmt.toString());
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
					}
					else {
						tempSmt.append("(bv2int (bvashr )");
					}
					
					i++;
				}

				temp = iter.next();

		//		System.out.println("dealing " + temp.getText());
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
	public String visitVarrefExpr(VarrefExprContext ctx) {
		String var = ctx.getText();
		var += getSubscript(var);
		return var;
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
				sub=this.visitMulExpr(ctx.args.get(i));
				sub=isCondition(sub);
				result.append("(" + opsList.get(i) + " " + sub);
			}
			sub= this.visitMulExpr(ctx.args.get(ctx.args.size() - 1));
			sub=isCondition(sub);
			result.append(" " +sub);
			for (int i = 0; i < opsList.size(); i++) {
				result.append(")");
			}
		}
		return result.toString();
	}

	private String isCondition(String sub) {
		List<String> conOpList=new ArrayList<String>();
		conOpList.add("or");conOpList.add("an");conOpList.add("=");conOpList.add("no");
		conOpList.add("<");conOpList.add("<=");conOpList.add(">");conOpList.add(">=");
		// (> 1 1)
		if(sub.trim().length()>3){
			String op=sub.trim().substring(1, 3).trim();
			if(conOpList.contains(op)){
				String result="(bti "+sub+")";
				return result;
			}else{
				return sub;
			}
		}else{
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
		// for(int i=0;i<ctx.getChildCount();i++){
		// System.out.println("haovc:"+ctx.getChild(i).getText());
		// }
		incSubscript(ctx.getChild(1).getText());
		return super.visitHavocStmt(ctx);
	}


	@Override
	public String visitOldExpr(OldExprContext ctx) {
		for (int i = 0; i < ctx.getChildCount(); i++) {
			System.out.println("Old: " + ctx.getChild(i).getText());
		}
		// return super.visitOldExpr(ctx);
		String varible = ctx.getChild(2).getText();
		return varible + this.getGlobaOldSubscript(varible);
	}
	/*
	@Override
	public String visitResultExpr(ResultExprContext ctx) {
		String varible = ctx.getChild(2).getText();
		return null;
	}*/

	/**
	 * 
	 * @param varible
	 * @return
	 */
	private int getGlobaOldSubscript(String varible) {
		int sub = 0;
		if (variCount.get(varible).size() < 3) {
			sub = 0;
		} else {
			sub = variCount.get(varible).get(2);
		}
		return sub;
	}

	private String getDeclStmt(String variName) {
		StringBuilder result = new StringBuilder();
		String typeName = "Int";
		result.append("(declare-fun ");
		result.append(variName + " ");
		result.append("() ");
		// for Int
		result.append(typeName + ")");
		// for Reals
//		result.append("Real"+")");
		result.append("\n");
		return result.toString();
	}

	/** Get current subscripte for a specific variable **/
	private int getSubscript(String text) {
		return variCount.get(text).get(1);
	}

	/** Increase the subscript while assigned **/
	private void incSubscript(String text) {
		// TODO : Declaration
		variCount.get(text).set(1, getSubscript(text) + 1);
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
	
	@SuppressWarnings("unchecked")
	private HashMap<String, ArrayList<Integer> > copyMap( Map<String, ArrayList<Integer> > ori) {
		 HashMap<String, ArrayList<Integer> > res = new HashMap<String, ArrayList<Integer> >();
		 
		 for ( Map.Entry<String, ArrayList<Integer> > entry : ori.entrySet()) {
			 res.put(entry.getKey(), (ArrayList<Integer>) entry.getValue().clone());
		 }
		 return res;
	}

	/** Return the whole SMT **/
	public String getSMT(){

		return smtResult.toString();
	}
}
