package parser;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import org.antlr.v4.runtime.Token;

import parser.SimpleCParser.AddExprContext;
import parser.SimpleCParser.AssertStmtContext;
import parser.SimpleCParser.AssignStmtContext;
import parser.SimpleCParser.AssumeStmtContext;
import parser.SimpleCParser.AtomExprContext;
import parser.SimpleCParser.BandExprContext;
import parser.SimpleCParser.BlockStmtContext;
import parser.SimpleCParser.BorExprContext;
import parser.SimpleCParser.BxorExprContext;
import parser.SimpleCParser.EqualityExprContext;
import parser.SimpleCParser.ExprContext;
import parser.SimpleCParser.FormalParamContext;
import parser.SimpleCParser.HavocStmtContext;
import parser.SimpleCParser.IfStmtContext;
import parser.SimpleCParser.LandExprContext;
import parser.SimpleCParser.LoopInvariantContext;
import parser.SimpleCParser.LorExprContext;
import parser.SimpleCParser.MulExprContext;
import parser.SimpleCParser.NumberExprContext;
import parser.SimpleCParser.OldExprContext;
import parser.SimpleCParser.ParenExprContext;
import parser.SimpleCParser.PrepostContext;
import parser.SimpleCParser.ProcedureDeclContext;
import parser.SimpleCParser.RelExprContext;
import parser.SimpleCParser.ResultExprContext;
import parser.SimpleCParser.ShiftExprContext;
import parser.SimpleCParser.StmtContext;
import parser.SimpleCParser.TernExprContext;
import parser.SimpleCParser.UnaryExprContext;
import parser.SimpleCParser.VarDeclContext;
import parser.SimpleCParser.VarrefExprContext;
import util.ProcessExec;
import util.ProcessTimeoutException;

public class TestVisitor extends SimpleCBaseVisitor<String> {
	private Map<String, ArrayList<Integer>> variCount;
	private Map<String, ProcedureDeclContext> procedureContext = new HashMap<String, ProcedureDeclContext>();
	private List<VarDeclContext> globals = new ArrayList<VarDeclContext>();
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
	private CallVisitor call = new CallVisitor();
	private List<String> requirList = new ArrayList<String>();
	private Map<String, String> resultProxyMap = new HashMap<String, String>();
	private int unboundDepth=10;
	// the fisrt string is proxy+i; the second string is the sentence of
	// assertion,
	// boolean represent is true or not
	private HashMap<String, String> proxyAssertMap = new HashMap<String, String>();

	private static final int TIMEOUT = 30;

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
		globals = ctx.globals;
		this.inProcedure = 0;
		StringBuffer finalProgramSMT = new StringBuffer();
		for (VarDeclContext item : gobls) {
			// resSmt.append(visitVarDecl(item));
			visitVarDecl(item);
		}

		for (ProcedureDeclContext item : procedures) {

			String name = item.name.getText();
			procedureContext.put(name, item);

		}
		this.inProcedure = 1;
		for (ProcedureDeclContext item : procedures) {
			String res = visitProcedureDecl(item);
			finalProgramSMT.append("(set-logic QF_IRA)\n");
			finalProgramSMT.append(getDivFunSMT());
			finalProgramSMT.append(getInttoBoolSmt());
			finalProgramSMT.append(getBooltoIntSmt());
			finalProgramSMT.append(getMyShiftLeft());
			finalProgramSMT.append(getMyShiftRight());
			finalProgramSMT.append(getDeclSMT(0));
			finalProgramSMT.append(res + "\n");
			finalProgramSMT.append("(check-sat)\n");
			finalProgramSMT.append(getWhichOneIsWrong());
			/* need to verified each procedure after generation */
			/* Todo */
			System.out.println("Program: \n" + finalProgramSMT.toString());
			smtCheckSat(finalProgramSMT.toString());
		}
		return resSmt.toString();
	}

	// TODO call
	@Override
	public String visitCallStmt(SimpleCParser.CallStmtContext ctx) {

		System.out.println("In Call Statement:: ");
		String methodName = ctx.callee.getText();
		String assignedVar = ctx.lhs.getText();
		List<ExprContext> actuals = ctx.actuals;
		StringBuffer postAssume = new StringBuffer();
		Map<String, String> exParameter = new HashMap<String, String>();

		if (procedureContext.containsKey(methodName)) {

			ProcedureDeclContext thisProcedure = procedureContext.get(methodName);

			for (int i = 0; i < actuals.size(); i++) {
				exParameter.put(thisProcedure.formals.get(i).name.getText(), actuals.get(i).getText());
			}

			for (VarDeclContext items : globals) {
				if (!exParameter.containsKey(items.name.getText())) {
					exParameter.put(items.name.getText(), items.name.getText());
				}
			}

			List<PrepostContext> contract = thisProcedure.contract;
			String assertion = this.assVisitor.getUnAssSMT();

			for (PrepostContext item : contract) {
				call.getAllVar(variCount, assignedVar, exParameter, thisProcedure);
				String smt = call.visitPrepost(item);
				if (item.getText().contains("requires")) {
					if (!smt.contains("(")) {
						smt = isNotCondition(smt);
					}
					if (this.ifLayer.size() != 0) {
						String finalTest = getIfSmt();
						finalTest = getAssertWithRequire(finalTest, true);
						finalTest = "(=> " + finalTest + " " + smt + ")";
						smt = finalTest;
					} else {
						smt = getAssertWithRequire(smt, false);
					}
					this.assVisitor.visitunnomAss(smt);
					this.assertList.add(smt);
				}
			}

			List<StmtContext> stmts = new ArrayList<StmtContext>();
			stmts = thisProcedure.stmts;

			for (int i = 0; i < stmts.size(); i++) {
				try {
					String assignVar = stmts.get(i).assignStmt().lhs.getText();
					for (VarDeclContext item : globals) {
						if (item.name.getText().equals(assignVar) && !item.name.getText().equals(assignedVar)) {
							variCount.get(assignVar).set(1, getSubscript(assignVar) + 1);
						}
					}

				} catch (NullPointerException e) {
				}
			}

			variCount.get(assignedVar).set(1, getSubscript(assignedVar) + 1);

			for (PrepostContext item : contract) {
				call.getAllVar(variCount, assignedVar, exParameter, thisProcedure);
				String smt = call.visitPrepost(item);
				if (item.getText().contains("ensures")) {
					if (!assertion.isEmpty())
						smt = "(assert (=> " + assertion + " " + smt + "))\n";
					else
						smt = "(assert " + smt + " )\n";
					postAssume.append(smt);
				}
			}
		}

		return postAssume.toString();
	}

	/**
	 * To get which one is wrong
	 * 
	 * @return
	 */
	private String getWhichOneIsWrong() {
		StringBuffer result = new StringBuffer();
		if (!this.assertList.isEmpty()) {
			result.append("(get-value (");
			for (int i = 0; i < this.assertList.size(); i++) {
				result.append("proxy" + i + " ");
			}
			return result.append("))").toString();
		} else {
			return "";
		}
	}

	private void smtCheckSat(String procSMT) {
		String vc = procSMT;
		ProcessExec process = new ProcessExec("z3", "-smt2", "-in");
		String queryResult = "";

		try {
			queryResult = process.execute(vc, TIMEOUT);
			if (!queryResult.contains("error")) {
				int indexofparr = queryResult.indexOf("(");
				String tempStr = queryResult.substring(indexofparr + 1, queryResult.length() - 2);
				String[] strIng = tempStr.split("\\)");
				for (String str : strIng) {
					String tempResult = str.replace('(', ' ').trim();
					String[] tempStrArray = tempResult.split(" ");
					resultProxyMap.put(tempStrArray[0], tempStrArray[1]);
				}
//				System.out.println(this.resultProxyMap);
//				System.out.println(this.proxyAssertMap);
			}
//			System.out.println(queryResult);
		} catch (ProcessTimeoutException | IOException | InterruptedException e) {
			System.out.println("UNKNOWN");
			System.exit(1);
		}

		if (queryResult.startsWith("sat")) {
			System.out.println("INCORRECT");
			System.exit(0);
		}

		if (!queryResult.startsWith("unsat")) {
			System.out.println("UNKNOWN");
//			System.out.println(queryResult);
			System.exit(1);
		}
	}

	// generate the function declaration
	private String getDivFunSMT() {
		StringBuilder result = new StringBuilder();
		result.append("(define-fun mydiv ((x Int) (y Int)) Int\n" + "(ite (= y 0) x (div x y)))\n");
		result.append("(define-fun mymod ((x Int) (y Int)) Int\n" + "(ite (= y 0) x (mod x y)))\n");
		return result.toString();
	}

	// generate the function declaration
	private String getInttoBoolSmt() {
		StringBuilder result = new StringBuilder();
		result.append("(define-fun itb ((x Int)) Bool\n");
		result.append("(ite (= x 0) false true))\n");
		return result.toString();
	}

	// generate the function declaration
	private String getBooltoIntSmt() {
		StringBuilder result = new StringBuilder();
		result.append("(define-fun bti ((x Bool)) Int\n");
		result.append("(ite (= x true) 1 0))\n");
		return result.toString();
	}

	// function for special shift problem
	private String getMyShiftLeft() {
		StringBuilder result = new StringBuilder();
		result.append("(define-fun myshl ((x Int) (y Int)) Int\n" + "(ite (or (>= y 32) (< y 0)) "
				+ "0 (bv2int (bvshl ((_ int2bv 32) x) ((_ int2bv 32) y)))))");
		result.append("\n");
		return result.toString();
	}

	// function for special shift problem
	private String getMyShiftRight() {
		StringBuilder result = new StringBuilder();
		result.append("(define-fun myashr ((x Int) (y Int)) Int\n" + "(ite (or (>= y 32) (< y 0)) "
				+ "0 (bv2int (bvashr ((_ int2bv 32) x) ((_ int2bv 32) y)))))");
		result.append("\n");
		return result.toString();
	}

	@Override
	public String visitPrepost(SimpleCParser.PrepostContext ctx) {
		super.visitPrepost(ctx);
		return null;
	}

	@Override
	public String visitRequires(SimpleCParser.RequiresContext ctx) {
		String requires;
		requires = super.visitRequires(ctx);
		this.requirList.add(requires);
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
		StringBuffer finalSMT = new StringBuffer();

		procName = ctx.name.toString();

		/*
		 * To generate the parameter of the procedure
		 */
		paras = ctx.formals;
		for (FormalParamContext para : paras) {
			String name = para.name.getText();
			resSmt.append(this.getDeclStmt(name));
			status.add(1);
			status.add(0);
			status.add(0);
			status.add(0);
			status.add(0);
			this.variCount.put(name, status);
		}
		////////////////////////
		initial = copyMap(this.variCount);
		////////////////////////
		/*
		 * To generate the pre condition
		 */
		int num = ctx.contract.size();
		for (int i = 0; i < num; i++) {
			if (ctx.contract.get(i).getText().contains("requires")) {
				super.visitPrepost(ctx.contract.get(i));
			}
		}
		preCombine();
		/*
		 * To generate the if,assign and so on SMT
		 */
		// the assign,if and so on SMT
		StringBuffer stmtSMT = new StringBuffer();
		for (int i = 0; i < ctx.stmts.size(); i++) {
			String temp = this.visitStmt(ctx.stmts.get(i));
			if (temp != null) {
				// System.out.println(temp);
				stmtSMT.append(temp);
			}
		}
		/*
		 * below is to generate the pre/post SMT
		 */
		returnExp = visitExpr(ctx.returnExpr);
		postNumber = 0;
		postCon = new ArrayList<String>();
		postSmtResult = new StringBuilder();

		for (int i = 0; i < num; i++) {
			if (ctx.contract.get(i).getText().contains("ensures")) {
				super.visitPrepost(ctx.contract.get(i));
			}
		}
		postCombine();

		// the decleration SMT
		// use varicount
		finalSMT.append(this.getDeclSMT(1));

		// print the assign,if and so on SMT
		finalSMT.append(stmtSMT.toString());

		// the assertion's SMT
		// use the chengyuan bianliang
		// finalSMT.append(this.getAssertNot());
		finalSMT.append(this.gettvUnAssSMT());

		return finalSMT.toString();
	}

	/**
	 * To replace every assertion by proxy i(i from 0 to n)
	 * 
	 * @return
	 */
	private String getAssertReplaced() {
		StringBuffer result = new StringBuffer();
		for (int i = 0; i < this.assertList.size(); i++) {
			this.proxyAssertMap.put("proxy" + i, this.assertList.get(i));
			String assVari = this.assertList.get(i);
			result.append("(declare-fun proxy" + i + " () Bool)\n" + "(assert (= proxy" + i + " " + assVari + "))\n");
		}
		return result.toString();
	}

	/**
	 * get the assertion
	 * 
	 * @return
	 */
	private String gettvUnAssSMT() {
		if (!this.assertList.isEmpty()) {
			String unnomRe = "proxy0";
			// in the below function,to generate the
			String finalResult = getAssertReplaced();
			for (int i = 1; i < this.assertList.size(); i++) {
				unnomRe = "(and " + "proxy" + i + " " + unnomRe + ")";
			}
			unnomRe = "(assert (not " + unnomRe + "))";
			return finalResult + unnomRe;
		} else {
			return "";
		}
	}

	/**
	 * get the Declaration SMT
	 * 
	 * @return
	 */
	private String getDeclSMT(int gloOrLocal) {
		// get declaration
		StringBuilder re = new StringBuilder();
		for (String key : this.variCount.keySet()) {
			if (this.variCount.get(key).get(0) == gloOrLocal) {
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
		status.add(0);
		status.add(0);
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
	/**
	 * 
	 * @param assStr
	 * @param flag:
	 *            true means is in IF; false means is an outside assertion
	 * @return
	 */
	private String getAssertWithRequire(String assStr, Boolean flag) {
		if (!this.requirList.isEmpty()) {
			String result = this.requirList.get(0);
			for (int i = 1; i < this.requirList.size(); i++) {
				String temp = this.requirList.get(i);
				result = "(and " + temp + " " + result + ")";
			}
			if (flag) {
				result = "(and " + result + " " + assStr + ")";
			} else {
				result = "(=> " + result + " " + assStr + ")";
			}
			return result;
		} else {
			return assStr;
		}
	}

	@Override
	public String visitAssertStmt(AssertStmtContext ctx) {
		String text = this.visitExpr(ctx.expr());

		if (!text.contains("(")) {
			text = isNotCondition(text);
		}

		if (this.ifLayer.size() != 0) {
			String finalTest = getIfSmt();
			finalTest = getAssertWithRequire(finalTest, true);
			finalTest = "(=> " + finalTest + " " + text + ")";
			text = finalTest;
		} else {
			text = getAssertWithRequire(text, false);
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

	private String gettvUnAssSMTforAssume() {
		if (!this.assertList.isEmpty()) {
			String result = this.assertList.get(0);
			for (int i = 1; i < this.assertList.size(); i++) {
				result = "(and " + result + " " + this.assertList.get(i) + ")";
			}
			return result;
		} else {
			return "";
		}
	}

	@Override
	public String visitAssumeStmt(AssumeStmtContext ctx) {

		String assertion = this.gettvUnAssSMTforAssume();

		String assumeSmt = this.visitExpr(ctx.expr());

		if (this.ifLayer.size() != 0) {
			String finalTest = getIfSmt();
			// for if
			finalTest = getAssertWithRequire(finalTest, true);
			String text = "";
			if (!assertion.isEmpty()) {
				text = "(=> " + assertion + " " + assumeSmt + ")";
			} else {
				text = assumeSmt;
			}
			// order is : if -> before assertion -> assume
			finalTest = "(assert (=> " + finalTest + " " + text + "))\n";
			return finalTest;
		} else {
			if (!assertion.isEmpty())
				assumeSmt = "(assert (=> " + assertion + " " + assumeSmt + "))\n";
			else
				assumeSmt = "(assert " + assumeSmt + " )\n";
			return assumeSmt;
		}
	}

	@Override
	// need finish ~~~~~
	public String visitVarDecl(VarDeclContext ctx) {
		String variName = ctx.getChild(1).getText();
		if (!this.variCount.keySet().contains(variName)) {
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
			// subscript
			status.add(0);
			// for old
			status.add(0);
			// for appeal
			status.add(0);
			// for if init
			status.add(0);
			
			variCount.put(variName, status);
			variName = variName + "0";
		} else {
			int subScriptnum = this.variCount.get(variName).get(1) + 1;
			this.variCount.get(variName).set(1, subScriptnum);
			variName = variName + subScriptnum;
		}
		String retSMT = "(declare-fun " + variName + " () " + "Int)\n";
		super.visitVarDecl(ctx);
		return "";
	}

	@Override
	public String visitAssignStmt(AssignStmtContext ctx) {

		String num = this.visitExpr((ExprContext) ctx.getChild(2));

		String name = ctx.getChild(0).getText();
		incSubscript(name);
		String variName = name + getSubscript(name);

		if (this.ifLayer.size() == 0) {
			incAppSubscript(name);
			setInitSubscript(name, getSubscript(name));
		}
		else {
			setAppSubscript(name);
		}

		StringBuilder unnomAss = new StringBuilder();
		StringBuilder nomoAss = new StringBuilder();
		num = isCondition(num);
		nomoAss.append("(assert (= " + variName + " " + num + "))\n");
		assVisitor.visitnomorAss(nomoAss.toString());
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

		String cond, strif, strelse, temp;

		/** store initial info of variable **/
		init = copyMap(this.variCount);

		/** receive condition SMT **/
		temp = ctx.condition.getText().toString();
		
		if(variCount.containsKey(ctx.condition.getText())) {
			cond = "(not (= " + temp + getSubscript(temp) + " 0))";
		} else {
			cond = super.visitExpr(ctx.condition);
		}

		/** prepare if information **/
		layer = this.ifLayer.size();
		iftemp = new HashMap<String, Integer>();
		iftemp.put(cond, 1);
		this.ifLayer.put(layer + 1, iftemp);

		/** visit if bloc statement **/
		strif = visitBlockStmt(ctx.thenBlock);

		resSmt.append(strif);
		/** store variable info after if **/
		afif = copyMap(this.variCount);

		/** detect else statement then enter **/
		if (ctx.elseBlock != null) {
			this.ifLayer.get(layer + 1).put(cond, 0);
			strelse = visitBlockStmt(ctx.elseBlock);
			resSmt.append(strelse);
		}

		/** Compare differences and generate Smt for if **/
		for (String key : afif.keySet()) {

			String tempSmt = "";

			if (init.containsKey(key) && afif.get(key).get(1) < this.variCount.get(key).get(1)) {
				tempSmt += "(assert (= " + key + (Integer.toString(this.variCount.get(key).get(1) + 1));
				tempSmt += " (ite " + cond + " " + key + Integer.toString(afif.get(key).get(1));
				tempSmt += " " + key + Integer.toString(this.variCount.get(key).get(1)) + ")))\n";
				incSubscript(key);
				incAppSubscript(key);
			} else if (init.containsKey(key) && afif.get(key).get(1) > init.get(key).get(3) && afif.get(key).get(1) == variCount.get(key).get(1)) {
				tempSmt += "(assert (= " + key + (Integer.toString(this.variCount.get(key).get(1) + 1));
				tempSmt += " (ite " + cond + " " + key + Integer.toString(afif.get(key).get(1));
				tempSmt += " " + key + Integer.toString((init.get(key).get(3))) + ")))\n";
				incSubscript(key);
				incAppSubscript(key);
			}

			resSmt.append(tempSmt);
		}

		if(layer == 0) {
			for (String var : variCount.keySet()) {
				setAppSubscript(var);
			}
		}
		
		this.ifLayer.remove(layer + 1);

		return resSmt.toString();
	}

	@Override
	public String visitWhileStmt(SimpleCParser.WhileStmtContext ctx) {
		StringBuilder res = new StringBuilder("");
		List<LoopInvariantContext> inVarList = new ArrayList<LoopInvariantContext>();
		String cond;

		cond = visitExpr(ctx.condition);

		for (LoopInvariantContext invar : inVarList) {

		}
		String whiCondition=ctx.condition.getText();
		
		StringBuffer finalResult=new StringBuffer();
		int i=0;
		while(i<this.unboundDepth){

		}
		this.assertList.add("false");
		this.assertList.add("false");

		return res.toString();
	}

	/*
	 * @Override(non-Javadoc)
	 * 
	 * @see parser.SimpleCBaseVisitor#visitLoopInvariant(parser.SimpleCParser.
	 * LoopInvariantContext)
	 *
	 * public String visitLoopInvariant(SimpleCParser.LoopInvariantContext ctx)
	 * { StringBuilder resSmt = new StringBuilder("");
	 * 
	 * 
	 * return resSmt.toString(); }
	 */

	@Override
	public String visitInvariant(SimpleCParser.InvariantContext ctx) {
		StringBuilder resSmt = new StringBuilder("");
		String text = this.visitExpr(ctx.condition);
		if (!text.contains("(")) {
			text = isNotCondition(text);
		}
		if (this.ifLayer.size() != 0) {
			String finalTest = getIfSmt();
			finalTest = getAssertWithRequire(finalTest, true);
			finalTest = "(=> " + finalTest + " " + text + ")";
			text = finalTest;
		} else {
			text = getAssertWithRequire(text, false);
		}
		this.assVisitor.visitunnomAss(text);
		this.assertList.add(text);
		;

		return "";
	}

	@Override
	public String visitBlockStmt(SimpleCParser.BlockStmtContext ctx) {
		StringBuilder res = new StringBuilder();

		for (StmtContext iter : ctx.stmts) {
			res.append(visitStmt(iter));
		}

		return res.toString();
	}

	@Override
	public String visitExpr(ExprContext ctx) {
		String resSmt;
		resSmt = this.visitTernExpr(ctx.ternExpr());
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

		String result = "";

		if (!sub.contains("(")) {
			result = "(itb " + sub + ")";
			return result;
		}
		if (sub.trim().length() > 3) {
			String op = sub.trim().substring(1, 3).trim();
			if (conOpList.contains(op)) {
				return sub;
			} else {
				result = "(itb " + sub + ")";
				return result;
			}
		} else {
			result = "(itb " + sub + ")";
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
						tempSmt.append("(myshl ");
					} else {
						tempSmt.append("(myashr ");
					}

					i++;
				}

				temp = iter.next();

				res = visitAddExpr(temp);

				if (tempSmt.length() == 0) {
					// resSmt.insert(resSmt.length() - i, " ((_ int2bv 32) " +
					// res + "))");
					resSmt.insert(resSmt.length() - i, " " + res + ")");
				} else {
					// tempSmt.insert(tempSmt.length() - 1, " ((_ int2bv 32) " +
					// res + ")");
					tempSmt.insert(tempSmt.length() - 1, " " + res);
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
		if (this.ifLayer.size() > 0) {
			var += getAppSubscript(var);
		} else {
			var += getSubscript(var);
		}

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

		String result = "";

		if (sub.trim().length() > 3) {
			String op = sub.trim().substring(1, 3).trim();
			if (conOpList.contains(op)) {
				result = "(bti " + sub + ")";
				return result;
			} 
			else {
				result = "(bti " + sub + ")";
				return result;
			}
		}

		return sub;
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
			String tempOop = token.getText();
			if (tempOop.equals("!")) {
				opsList.add("not");
			} else {
				opsList.add(tempOop);
			}
		}
		
		if (opsList.isEmpty())
		{
			return this.visitAtomExpr((AtomExprContext) ctx.getChild(0));
		} else {
			for (int i = 0; i < opsList.size(); i++) {
				switch (opsList.get(i)) {
				case "~":
					result.append("(bv2int (" + opsList.get(i) + " ");
					result.append(" ((_ int2bv 32)" + this.visitAtomExpr(ctx.arg) + ")))");
					break;
				default:
					result.append("(" + opsList.get(i) + " ");
					result.append(" " + this.isNotCondition(this.visitAtomExpr(ctx.arg)));
					result.append(")");
				}
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

	/** Get current subscript for a specific variable **/
	private int getSubscript(String text) {
		return variCount.get(text).get(1);
	}

	/** Increase the subscript while assigned **/
	private void incSubscript(String text) {
		// TODO : Declaration
		variCount.get(text).set(1, getSubscript(text) + 1);
	}

	/** Get current available subscript when visit value **/
	private int getAppSubscript(String text) {
		return variCount.get(text).get(3);
	}

	/** Increase the subscript for available subscript **/
	private void incAppSubscript(String text) {
		variCount.get(text).set(3, getAppSubscript(text) + 1);
	}

	/** set the subscript value equal to assignment **/
	private void setAppSubscript(String text) {
		variCount.get(text).set(3, getSubscript(text));
	}

	/** set the subscript value before enter if **/
	private void setInitSubscript(String text, int value) {
		variCount.get(text).set(4, value);
	}

	/** return the subscript value before enter if **/
	private int getInitSubscript(String text) {
		return variCount.get(text).get(4);
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
	
	/* generate smt of unwind 1 layer of while statement 
	 * Para: Condition Context, Block statementContext 
	 * Return: string of "if" SMT 
	 */
	private String getUnwindIf(SimpleCParser.ExprContext cond, SimpleCParser.BlockStmtContext ctx) {
		StringBuilder resSmt = new StringBuilder();
		HashMap<String, ArrayList<Integer>> init = new HashMap<String, ArrayList<Integer>>();
		HashMap<String, Integer> iftemp;
		String condition = "";
		String strif;
		int layer;
		init = copyMap(this.variCount);
		
		if(variCount.containsKey(cond.getText())) {
			condition = "(not (= " + cond.getText() + getSubscript(cond.getText()) + " 0))";
		} else {
			condition = super.visitExpr(cond);
		}

		/** prepare if information **/
		layer = this.ifLayer.size();
		iftemp = new HashMap<String, Integer>();
		iftemp.put(condition, 1);
		this.ifLayer.put(layer + 1, iftemp);

		/** visit bloc statement **/
		strif = visitBlockStmt(ctx);

		resSmt.append(strif);

		/** Compare differences and generate Smt for if **/
		for (String key : this.variCount.keySet()) {

			String tempSmt = "";

			if (init.containsKey(key) && this.variCount.get(key).get(1) > init.get(key).get(3)) {
				tempSmt += "(assert (= " + key + (Integer.toString(this.variCount.get(key).get(1) + 1));
				tempSmt += " (ite " + cond + " " + key + Integer.toString(this.variCount.get(key).get(1));
				tempSmt += " " + key + Integer.toString((init.get(key).get(3))) + ")))\n";
				incSubscript(key);
				incAppSubscript(key);
			}

			resSmt.append(tempSmt);
		}

		if(layer == 0) {
			for (String var : variCount.keySet()) {
				setAppSubscript(var);
			}
		}
		
		this.ifLayer.remove(layer + 1);
		
		
		return resSmt.toString();
	}
	

	/** Return the whole SMT **/
	public String getSMT() {

		return smtResult.toString();
	}

	// private String getAssertNot() {
	// String postSMT = this.postSmtResult.toString();
	// String mavSMT = this.gettvUnAssSMT();
	// StringBuffer result = new StringBuffer();
	// if (postSMT.isEmpty() || postSMT.equals("null")) {
	// if (mavSMT.isEmpty()) {
	// result.append("(assert false)");
	// } else {
	// result.append("(assert (not ");
	// result.append(mavSMT);
	// result.append("))");
	// }
	// } else {
	// if (mavSMT.isEmpty()) {
	// result.append("(assert (not ");
	// result.append(postSMT);
	// result.append("))");
	// } else {
	// result.append("(assert (not (and");
	// result.append(postSMT);
	// result.append(mavSMT);
	// result.append(")))");
	// }
	// }
	// return result.toString();
	// }
}
