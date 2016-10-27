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


	public TestVisitor() {
		this.smtResult = new StringBuilder();
	}

	public TestVisitor(MyAssertVisitor assVisitor, VariCount variCount, String glSmt, String plSmt) {
		this.assVisitor = assVisitor;
		this.variCount = variCount.getVarCount();
		this.smtResult = new StringBuilder();
		this.smtResult.append(glSmt);
		this.smtResult.append(plSmt);

	}

	public TestVisitor(MyAssertVisitor assVisitor, VariCount variCount) {
		this.assVisitor = assVisitor;
		this.variCount = variCount.getVarCount();
		this.smtResult = new StringBuilder();
	}

	@Override
	public String visitAssertStmt(AssertStmtContext ctx) {
		String text = this.visitExpr(ctx.expr());
		System.out.println("assert:++++++++" + text);
		this.assVisitor.visitunnomAss(text);
		return null;
	}

	// 声明语句的SMT转换
	@Override
	public String visitVarDecl(VarDeclContext ctx) {
		// SMT语句结果
		StringBuilder result = new StringBuilder();
		// 只有一种类型，所以不用特地处理类型名
		// 变量名
		String variName = ctx.getChild(1).getText();
		ArrayList<Integer> status = new ArrayList<Integer>();
		status.add(1);
		status.add(0);
		// 变量名，下标初始为0
		variCount.put(variName, status);
		variName = variName + "0";
		// 编写SMT语句
		result.append(getDeclStmt(variName));
		// 调用父类
		super.visitVarDecl(ctx);
		// 拼接完整SMT语句
		smtResult.append(result.toString());
		return null;
	}

	// 赋值语句的SMT转换
	@Override
	public String visitAssignStmt(AssignStmtContext ctx) {

		// String num = ctx.getChild(2).getText();
		// 右边的表达式语句
		String num = this.visitExpr((ExprContext) ctx.getChild(2));

		// 被赋值的变量名，且取下标
		String name = ctx.getChild(0).getText();
		String variName = name + getSubscript(name);

		incSubscript(name);

		// not类型的assert.
		StringBuilder unnomAss = new StringBuilder();

		// 普通类型的assert
		StringBuilder nomoAss = new StringBuilder();
		// 赋值语句
		nomoAss.append("(assert (= " + variName + " " + num + "))\n");
		assVisitor.visitnomorAss(nomoAss.toString());

		// 判断是否超过限制
		unnomAss.append("(<= " + variName + " 4294967295)");
		unnomAss.append("(>= " + variName + " 0)");
		assVisitor.visitunnomAss(unnomAss.toString());
		// 下标问题
		return nomoAss.toString();
	}
	
	@Override
	public String visitIfStmt(IfStmtContext ctx) {
		Map<String, ArrayList<Integer>> init = new HashMap<String, ArrayList<Integer>>();
		Map<String, ArrayList<Integer>> afif = new HashMap<String, ArrayList<Integer>>();
		StringBuilder resSmt = new StringBuilder("");
		String cond, strif, strelse;
		
		init = copyMap(this.variCount);
//		System.out.println(ctx.condition.getText());		
		cond = super.visitExpr(ctx.condition);
		
//		System.out.println("cond :" + cond);
		strif = visitBlockStmt(ctx.thenBlock);
		smtResult.append(strif);
		afif = copyMap(this.variCount);
	//	System.out.println("strif :" + strif);
	//	System.out.println("afif: " + afif + "      this.vari " + variCount);
		
		if(ctx.elseBlock != null) {
			strelse = visitBlockStmt(ctx.elseBlock);
			smtResult.append(strelse);
		//	System.out.println("strelse :" + strelse);
	//		System.out.println("afif: " + afif + "      this.vari " + variCount);
			for(String key : afif.keySet()) {
	//			System.out.println("key: " + key + " " + afif.get(key).get(1));
				String tempSmt = "";
				if(afif.get(key).get(1) > this.variCount.get(key).get(1)) {
					tempSmt += "(assert (= " + key + Integer.toString(afif.get(key).get(1) + 1);
					tempSmt += " (ite " + cond + " " + key + Integer.toString(afif.get(key).get(1));
					tempSmt += " " + key + Integer.toString(this.variCount.get(key).get(1)) + "))\n";
					incSubscript(key);
					incSubscript(key);
					System.out.println("tmp res : " + tempSmt.toString());
				}
				else if(afif.get(key).get(1) < this.variCount.get(key).get(1)) {
					tempSmt += "(assert (= " + key + Integer.toString(this.variCount.get(key).get(1) + 1);
					tempSmt += " (ite " + cond + " " + key + Integer.toString(this.variCount.get(key).get(1));
					tempSmt += " " + key + Integer.toString(afif.get(key).get(1)) + "))\n";
					incSubscript(key);
					incSubscript(key);
					System.out.println("tmp res : " + tempSmt.toString());
				}
				else if(afif.get(key).get(1) > init.get(key).get(1)) {
					tempSmt += "(assert (= " + key + Integer.toString(this.variCount.get(key).get(1) + 1);
					tempSmt += " (ite " + cond + " " + key + Integer.toString(afif.get(key).get(1));
					tempSmt += " " + key + Integer.toString(init.get(key).get(1)) + "))\n";
					incSubscript(key);
					incSubscript(key);
				}
				
				resSmt.append(tempSmt);
			}
		}


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
	//	 System.out.println("expr is " + resSmt + " " + ctx.getText());
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
			resSmt.append("(ite )");
			Iterator<LorExprContext> iter = ctx.args.iterator();
			while (iter.hasNext()) {
				LorExprContext temp;
				temp = iter.next();

//				System.out.println("dealing " + temp.getText());
				res = visitLorExpr(temp);
//				System.out.println("res " + res + "   " + ctx.getText());
				resSmt.insert(resSmt.length() - 1, " " + res);

			}

	//		System.out.println("answer " + resSmt.toString() + " " + ctx.getText());

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
					resSmt.insert(resSmt.length() - i, " " + res);
				} else {
					tempSmt.insert(tempSmt.length() - 1, res);
					resSmt.insert(resSmt.length() - i + 1, " " + tempSmt);
				}

			}
		}
		
		System.out.println("result " + resSmt.toString());
		return resSmt.toString();

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
					resSmt.insert(resSmt.length() - i, " " + res);
				} else {
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
					tempSmt.append("(bvor )");
					i++;
				}

				temp = iter.next();

				System.out.println("dealing " + temp.getText());
				res = visitBxorExpr(temp);

				if (tempSmt.length() == 0) {
					resSmt.insert(resSmt.length() - i, " " + res);
				} else {
					tempSmt.insert(tempSmt.length() - 1, res);
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
					tempSmt.append("(bvxor )");
					i++;
				}

				temp = iter.next();

			//	System.out.println("dealing " + temp.getText());
				res = visitBandExpr(temp);

				if (tempSmt.length() == 0) {
					resSmt.insert(resSmt.length() - i, " " + res);
				} else {
					tempSmt.insert(tempSmt.length() - 1, res);
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
					tempSmt.append("(bvand )");
					i++;
				}

				temp = iter.next();
				System.out.println("dealing " + temp.getText());
				res = visitEqualityExpr(temp);

				if (tempSmt.length() == 0) {
					resSmt.insert(resSmt.length() - i, " " + res);
				} else {
					tempSmt.insert(tempSmt.length() - 1, res);
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
			while (iter.hasNext()) {
				StringBuilder tempSmt = new StringBuilder("");
				RelExprContext temp;

				if (i < ctx.ops.size()) {
					if (ctx.ops.get(i).toString().equals("==")) {
						tempSmt.append("(= )");
					}
					else {
						tempSmt.append("(not )");
					}			
					i++;
				}

				temp = iter.next();

//				System.out.println("dealing " + temp.getText());
				res = visitRelExpr(temp);

				if (tempSmt.length() == 0) {
					resSmt.insert(resSmt.length() - i, " " + res);
				} else {
					tempSmt.insert(tempSmt.length() - 1, res);
					resSmt.insert(resSmt.length() - i + 1, " " + tempSmt);
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
			Iterator<ShiftExprContext> iter = ctx.args.iterator();
			int i = 0;
			while (iter.hasNext()) {
				StringBuilder tempSmt = new StringBuilder("");
				ShiftExprContext temp;

				if (i < ctx.ops.size()) {
					tempSmt.append("(" + ctx.ops.get(i).toString() + " )");
					i++;
				}

				temp = iter.next();
		//		System.out.println("dealing " + temp.getText());
				res = visitShiftExpr(temp);

				if (tempSmt.length() == 0) {
					resSmt.insert(resSmt.length() - i, " " + res);
				} else {
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
			resSmt.append("(or )");
			Iterator<AddExprContext> iter = ctx.args.iterator();
			int i = 0;
			while (iter.hasNext()) {
				StringBuilder tempSmt = new StringBuilder("");
				AddExprContext temp;

				if (i < ctx.ops.size()) {
					if (ctx.ops.get(i).toString().equals("<<")) {
						tempSmt.append("(bvshl )");
					}
					else {
						tempSmt.append("(bvlshr )");
					}
					
					i++;
				}

				temp = iter.next();

				System.out.println("dealing " + temp.getText());
				res = visitAddExpr(temp);

				if (tempSmt.length() == 0) {
					resSmt.insert(resSmt.length() - i, " " + res);
				} else {
					tempSmt.insert(tempSmt.length() - 1, res);
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
		if (getSubscript(var) > 0) {
			var += getSubscript(var) - 1;
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
		 * 注意，没有操作符，就没有操作数
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
			for (int i = 0; i < opsList.size(); i++) {
				result.append("(" + opsList.get(i) + " " + this.visitMulExpr(ctx.args.get(i)));
			}
			result.append(" " + this.visitMulExpr(ctx.args.get(ctx.args.size() - 1)));
			for (int i = 0; i < opsList.size(); i++) {
				result.append(")");
			}
		}
		return result.toString();
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
				// 不能用%，只能用mod
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
		// havoc的 SMT语句：
		// 将对应变量的下标+1即可
		incSubscript(ctx.getChild(1).getText());
		return super.visitHavocStmt(ctx);
	}


	// 只能用在全局变量中
	@Override
	public String visitOldExpr(OldExprContext ctx) {
		for (int i = 0; i < ctx.getChildCount(); i++) {
			System.out.println("Old: " + ctx.getChild(i).getText());
		}
		// return super.visitOldExpr(ctx);
		String varible = ctx.getChild(2).getText();
		return varible + this.getGlobaOldSubscript(varible);
	}

	// 只能用在全局变量中
	@Override
	public String visitResultExpr(ResultExprContext ctx) {
		String varible = ctx.getChild(2).getText();
		return null;
	}

	/**
	 * 拿到全局变量进入方法前的值 令variCount 对应内容的List的第三个值存储这个内容
	 * 
	 * @param varible
	 * @return
	 */
	private int getGlobaOldSubscript(String varible) {
		int sub = 0;
		if (variCount.get(varible).size() < 3) {
			// 对于多个procedure而言，有问题
			// 对于单个procedure而言，暂时没有问题。
			sub = 0;
		} else {
			sub = variCount.get(varible).get(2);
		}
		return sub;
	}

	// 获取声明语句的SMT语句
	private String getDeclStmt(String variName) {
		StringBuilder result = new StringBuilder();
		String typeName = "Int";
		// 编写SMT语句
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
