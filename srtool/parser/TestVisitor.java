package parser;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import org.antlr.v4.runtime.Token;

import parser.SimpleCParser.*;

public class TestVisitor extends SimpleCBaseVisitor<String> {
	private Map<String, ArrayList<Integer>> variCount;
	private StringBuilder smtResult;
	private MyAssertVisitor assVisitor;
	private HashMap<Integer, HashMap<String, Integer>> ifLayer;
	private ArrayList<String> preCon = new ArrayList<String>();
	private ArrayList<String> postCon = new ArrayList<String>();
	private StringBuilder preSmtResult = new StringBuilder();
	private StringBuilder postSmtResult = new StringBuilder();
	private int postNumber = 0;
	private int preNumber = 0;
	private int inProcedure;
	private String returnExp;
	private List<String> assertList = new ArrayList<String>();

	public TestVisitor() {
		postNumber = 0;
		this.smtResult = new StringBuilder();
		this.preSmtResult = new StringBuilder();
	}

	public TestVisitor(MyAssertVisitor assVisitor, VariCount variCount, String glSmt, String plSmt) {
		this.assVisitor = assVisitor;
		this.variCount = variCount.getVarCount();
		this.ifLayer = variCount.getIfLayer();
		this.smtResult = new StringBuilder();
	}

	public TestVisitor(MyAssertVisitor assVisitor, VariCount variCount) {
		this.assVisitor = assVisitor;
		this.variCount = variCount.getVarCount();
		this.ifLayer = variCount.getIfLayer();
		this.smtResult = new StringBuilder();
	}

	/////////////////////////////////
	public String getPreSMT() {
		return preSmtResult.toString();
	}

	public void preCombine() {

		preSmtResult = new StringBuilder();

		for (int i = 0; i < preNumber - 1; i++) {
			preSmtResult.append(" (and ");
		}
		if (!preCon.isEmpty()) {
			preSmtResult.append(preCon.get(0));
		}
		for (int i = 1; i < preNumber; i++) {
			preSmtResult.append(preCon.get(i) + ") ");
		}
	}

	@Override
	public String visitProgram(SimpleCParser.ProgramContext ctx) {
		StringBuilder resSmt = new StringBuilder("");
		List<VarDeclContext> gobls = ctx.globals;
		List<ProcedureDeclContext> procedures = ctx.procedures;
		this.inProcedure = 0;
		for (VarDeclContext item : gobls) {
			resSmt.append(visitVarDecl(item));
		}

		this.inProcedure = 1;
		for (ProcedureDeclContext item : procedures) {
			String res = visitProcedureDecl(item);
			resSmt.append(res);

			/* need to verified each procedure after generation */
			/* Todo */
		}

		return resSmt.toString();
	}

	@Override
	public String visitPrepost(SimpleCParser.PrepostContext ctx) {
		for (int i = 0; i < ctx.getChildCount(); i++) {
			System.out.println("PrePost: " + ctx.getChild(i).getText());
		}
		super.visitPrepost(ctx);
		return null;
	}

	@Override
	public String visitRequires(SimpleCParser.RequiresContext ctx) {
		String requires;
		requires = super.visitRequires(ctx);

		preNumber++;
		preCon.add(requires);
		return null;
	}

	public String visitProcedureDecl(SimpleCParser.ProcedureDeclContext ctx) {
		StringBuilder resSmt = new StringBuilder("");
		List<FormalParamContext> paras;
		List<StmtContext> stmts;
		ArrayList<Integer> status = new ArrayList<Integer>();
		Map<String, ArrayList<Integer>> initial = new HashMap<String, ArrayList<Integer>>();
		String procName;

		procName = ctx.name.toString();

		paras = ctx.formals;
		for (FormalParamContext para : paras) {
			String name = para.name.getText();
			resSmt.append(this.getDeclStmt(name));
			status.add(1);
			status.add(0);
			this.variCount.put(name, status);
		}

		initial = copyMap(this.variCount);

		stmts = ctx.stmts;
		for (StmtContext stmt : stmts) {
			String res = visitStmt(stmt);
			resSmt.append(res);
		}

		returnExp = visitExpr(ctx.returnExpr);
		postNumber = 0;
		postCon = new ArrayList<String>();
		postSmtResult = new StringBuilder();
		int num = ctx.contract.size();
		for (int i = 0; i < num; i++) {
			if (ctx.contract.get(i).getText().contains("requires")) {
				super.visitPrepost(ctx.contract.get(i));
			}
		}
		preCombine();

		for (int i = 0; i < num; i++) {
			if (ctx.contract.get(i).getText().contains("ensures")) {
				super.visitPrepost(ctx.contract.get(i));
			}
		}
		postCombine();
		/* wait to change return prepost */

		// the decleration SMT
		// use varicount
		System.out.print("FinalResult: \n" + this.getDeclSMT());

		// the assign,if and so on SMT
//		System.out.print(this.smtResult.toString());
		for (int i = 0; i < ctx.stmts.size(); i++) {
			String temp = this.visitStmt(ctx.stmts.get(i));
			if (temp != null) {
				System.out.println(temp);
			}
		}
		// the assertion's SMT
		// use the chengyuan bianliang
		System.out.println(getAssertNot());
		System.out.println();
		return null;
	}

	private String gettvUnAssSMT() {
		if (!this.assertList.isEmpty()) {
			// return "(and "+unnomAss.append(" )").toString();
			String unnomRe = this.assertList.get(0);
			for (int i = 1; i < this.assertList.size(); i++) {
				unnomRe = "(and " + this.assertList.get(i) + " " + unnomRe + ")";
			}
			return unnomRe;
		} else {
			return "";
		}
	}

	private String getAssertNot() {
		String postSMT = this.postSmtResult.toString();
		String mavSMT = this.gettvUnAssSMT();
		StringBuffer result = new StringBuffer();
		if (postSMT.isEmpty() || postSMT.equals("null")) {
			if (mavSMT.isEmpty()) {
				result.append("(assert false)");
			} else {
				result.append("(assert (not ");
				result.append(mavSMT);
				result.append("))");
			}
		} else {
			if (mavSMT.isEmpty()) {
				result.append("(assert (not ");
				result.append(postSMT);
				result.append("))");
			} else {
				result.append("(assert (not (and");
				result.append(postSMT);
				result.append(mavSMT);
				result.append(")))");
			}
		}
		return result.toString();
	}

	/**
	 * get the Declaration SMT
	 * 
	 * @return
	 */
	private String getDeclSMT() {
		// get declaration
		StringBuilder re = new StringBuilder();
		for (String key : this.variCount.keySet()) {
			List<Integer> varList = this.variCount.get(key);
			if (varList.get(1) == 0) {
				re.append("(declare-fun ");
				re.append(key + 0 + " ");
				re.append("() ");
				re.append("Int" + ")");
				re.append("\n");
			} else {
				for (int i = 0; i < 1 + varList.get(1); i++) {
					re.append("(declare-fun ");
					re.append(key + i + " ");
					re.append("() ");
					re.append("Int" + ")");
					re.append("\n");
				}
			}
		}
		return re.toString();
	}

	@Override
	public String visitFormalParam(FormalParamContext ctx) {
		String variName = ctx.getChild(1).getText();
		String typeName = "Int";
		StringBuffer result = new StringBuffer();
		result.append("(declare-fun ");
		result.append(variName + "0");
		result.append(" () ");
		result.append(typeName + ")");
		result.append("\n");
		ArrayList<Integer> status = new ArrayList<Integer>();
		status.add(1);
		status.add(0);
		this.variCount.put(variName, status);
		// return result.toString();
		return null;
	}

	public String getPostSMT() {
		return postSmtResult.toString();
	}

	public void postCombine() {

		if (postCon.isEmpty()) {
			postSmtResult.append("null");
		} else {
			// postSmtResult = new StringBuilder();
			// for(int i =0 ; i< postNumber-1; i++){
			// postSmtResult.append(" (and ");
			// }
			for (int i = 0; i < postCon.size(); i++) {
				this.assertList.add(postCon.get(i));
				assVisitor.visitunnomAss(postCon.get(i));
			}
			// postSmtResult.append(postCon.get(0));
			// for(int i =1 ; i< postNumber; i++){
			// postSmtResult.append(postCon.get(i) + ")");
			// }
		}
	}

	@Override
	public String visitEnsures(SimpleCParser.EnsuresContext ctx) {
		String ensures;
		StringBuilder ensuresSMT = new StringBuilder();
		ensures = super.visitEnsures(ctx);

		if (!(preSmtResult.length() == 0)) {
			ensuresSMT.append("(=> ");
			ensuresSMT.append(preSmtResult);
			ensuresSMT.append(ensures);
			ensuresSMT.append(") ");
		} else {
			ensuresSMT.append(ensures);
		}
		postNumber++;
		postCon.add(ensuresSMT.toString());
		return null;
	}

	@Override
	public String visitResultExpr(ResultExprContext ctx) {

		return returnExp;
	}

	//////////////////////////////////

	@Override
	public String visitAssertStmt(AssertStmtContext ctx) {
		String text = this.visitExpr(ctx.expr());
		if (this.ifLayer.size() != 0) {
			String finalTest = getIfSmt();
			finalTest = "(=> " + finalTest + " " + text + ")";
			text = finalTest;
		}
		if (!text.contains("(")) {
			text = isNotCondition(text);
		}
		this.assVisitor.visitunnomAss(text);
		this.assertList.add(text);
		return "";
	}

	private String getIfSmt() {
		List<String> ifList = new ArrayList<String>();
		String finalTest = "";
		/**
		 * Hash<Integer,Hash<String,Integer>> The first HashMap's key is the
		 * layer; inner hash, the key means condition,the integer means whether
		 * in if or else
		 */
		for (Integer keyInt : this.ifLayer.keySet()) {
			String tempStr = "";
			for (String str : this.ifLayer.get(keyInt).keySet()) {
				int flagif = this.ifLayer.get(keyInt).get(str);
				if (flagif == 1) {
					tempStr = str;
				} else {
					tempStr = "(not " + str + ")";
				}
			}
			ifList.add(tempStr);
		}

		if (ifList.size() != 0) {
			if (ifList.size() == 1) {
				finalTest = ifList.get(0);
			} else {
				finalTest = ifList.get(0);
				for (int i = 1; i < ifList.size(); i++) {
					finalTest = "(and " + finalTest + " " + ifList.get(i) + ")";
				}
			}
		}
		return finalTest;
	}

	@Override
	public String visitAssumeStmt(AssumeStmtContext ctx) {

		String text = this.visitExpr(ctx.expr());
		text = ("(assert " + text + ")\n");
		this.smtResult.append(text);
		return null;
	}

	@Override
	// need finish ~~~~~
	public String visitVarDecl(VarDeclContext ctx) {
		StringBuilder result = new StringBuilder();
		String variName = ctx.getChild(1).getText();
		ArrayList<Integer> status = new ArrayList<Integer>();

		// Declaration global
		if (inProcedure == 0) {
			status.add(0);
		}
		// Declaration in procedure
		else {
			status.add(1);
		}

		// if we dont want to be to clear to reader XD, we can do this XD
		// status.add(inProcedure);
		// XD
		status.add(0);
		variCount.put(variName, status);
		variName = variName + "0";
		String retSMT = "(declare-fun " + variName + " () " + "Int)\n";
		super.visitVarDecl(ctx);
		return null;
	}

	@Override
	public String visitAssignStmt(AssignStmtContext ctx) {

		String num = this.visitExpr((ExprContext) ctx.getChild(2));

		String name = ctx.getChild(0).getText();
		incSubscript(name);
		String variName = name + getSubscript(name);
		StringBuilder unnomAss = new StringBuilder();
		StringBuilder nomoAss = new StringBuilder();
		num = isCondition(num);
		nomoAss.append("(assert (= " + variName + " " + num + "))\n");
		// assVisitor.visitnomorAss(nomoAss.toString());
		this.smtResult.append(nomoAss.toString());
		// here is for the checking whether it is out of bound
		unnomAss.append("(<= " + variName + " 4294967295)");
		unnomAss.append("(>= " + variName + " 0)");

		
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
		String text = "";

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
		text += strif;
		// smtResult.append(strif);

		/** store variable info after if **/
		afif = copyMap(this.variCount);

		/** detect else statement then enter **/
		if (ctx.elseBlock != null) {
			this.ifLayer.get(layer + 1).put(cond, 0);
			strelse = visitBlockStmt(ctx.elseBlock);
			// smtResult.append(strelse);
			text += strelse;
		}
		/** Compare differences and generate Smt for if **/
		for (String key : afif.keySet()) {

			String tempSmt = "";
			if (afif.get(key).get(1) > this.variCount.get(key).get(1)) {
				tempSmt += "(assert (= " + key + (Integer.toString(afif.get(key).get(1) + 1));
				tempSmt += " (ite " + cond + " " + key + Integer.toString(afif.get(key).get(1));
				tempSmt += " " + key + Integer.toString(this.variCount.get(key).get(1)) + "))\n";
				incSubscript(key);
			} else if (afif.get(key).get(1) < this.variCount.get(key).get(1)) {
				tempSmt += "(assert (= " + key + (Integer.toString(this.variCount.get(key).get(1) + 1));
				tempSmt += " (ite " + cond + " " + key + Integer.toString(this.variCount.get(key).get(1));
				tempSmt += " " + key + Integer.toString(afif.get(key).get(1)) + ")))\n";
				incSubscript(key);
			} else if (afif.get(key).get(1) > init.get(key).get(1)) {
				tempSmt += "(assert (= " + key + (Integer.toString(this.variCount.get(key).get(1) + 1));
				tempSmt += " (ite " + cond + " " + key + Integer.toString(afif.get(key).get(1));
				tempSmt += " " + key + Integer.toString((init.get(key).get(1))) + ")))\n";
				incSubscript(key);
			}
			resSmt.append(tempSmt);
		}
		text += resSmt;

		this.ifLayer.remove(layer + 1);

		smtResult.append(resSmt);
		// return resSmt.toString();
		return text;
	}

	@Override
	public String visitBlockStmt(BlockStmtContext ctx) {
		StringBuilder res = new StringBuilder();

		for (StmtContext iter : ctx.stmts) {
			res.append(visitStmt(iter));
		}

		return res.toString();
	}

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
		return varible + this.getGlobaOldSubscript(varible);
	}

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
		// result.append("Real"+")");
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
	private HashMap<String, ArrayList<Integer>> copyMap(Map<String, ArrayList<Integer>> ori) {
		HashMap<String, ArrayList<Integer>> res = new HashMap<String, ArrayList<Integer>>();

		for (Map.Entry<String, ArrayList<Integer>> entry : ori.entrySet()) {
			res.put(entry.getKey(), (ArrayList<Integer>) entry.getValue().clone());
		}
		return res;

	}

	/** Return the whole SMT **/
	public String getSMT() {

		return smtResult.toString();
	}
}
