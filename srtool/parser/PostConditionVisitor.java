package parser;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import org.antlr.v4.runtime.Token;

import parser.SimpleCParser.AddExprContext;
import parser.SimpleCParser.AtomExprContext;
import parser.SimpleCParser.BandExprContext;
import parser.SimpleCParser.BorExprContext;
import parser.SimpleCParser.BxorExprContext;
import parser.SimpleCParser.EqualityExprContext;
import parser.SimpleCParser.ExprContext;
import parser.SimpleCParser.LandExprContext;
import parser.SimpleCParser.LorExprContext;
import parser.SimpleCParser.MulExprContext;
import parser.SimpleCParser.NumberExprContext;
import parser.SimpleCParser.ParenExprContext;
import parser.SimpleCParser.RelExprContext;
import parser.SimpleCParser.ResultExprContext;
import parser.SimpleCParser.ShiftExprContext;
import parser.SimpleCParser.TernExprContext;
import parser.SimpleCParser.UnaryExprContext;
import parser.SimpleCParser.VarrefExprContext;

public class PostConditionVisitor extends SimpleCBaseVisitor<String> {

	private Map<String, ArrayList<Integer>> variCount;
	private StringBuilder smtResult = new StringBuilder();
	private ArrayList<String> postCon = new ArrayList<String>();
	private String requiresSMT;
	private String returnExp;
	
	
	private int postNumber = 0;
	
	public PostConditionVisitor(String requiresSMT, VariCount variCount){
		
		this.requiresSMT = requiresSMT; 
		this.variCount = variCount.getVarCount();
	}
	
	public String getSMT(){
		
		return smtResult.toString();
		
	}
	
	public void combine (){
		
		if(postCon.isEmpty()){
			
			smtResult.append("null");
			
		}else{		
			
			smtResult = new StringBuilder();
			for(int i =0 ; i< postNumber-1; i++){
				smtResult.append(" (and ");
			}
			
			smtResult.append(postCon.get(0));
			
			for(int i =1 ; i< postNumber; i++){
				smtResult.append(postCon.get(i) + ")");
			}
			
		}
	}
	
	
	public String visitProcedureDecl (SimpleCParser.ProcedureDeclContext ctx){
		
		int child_num = ctx.getChildCount()-3;
						
		returnExp = super.visitExpr((ExprContext)ctx.getChild(child_num));
		super.visitProcedureDecl(ctx);
		System.out.println("return :: " + returnExp);
		
		return null;
	}	
	
	@Override
	public String visitEnsures (SimpleCParser.EnsuresContext ctx){
	
		String ensures;	
		StringBuilder ensuresSMT = new StringBuilder();
		ensures = super.visitEnsures(ctx);
		
		if(!requiresSMT.equals("null")){
			ensuresSMT.append("(=> ");
			ensuresSMT.append(requiresSMT);
			ensuresSMT.append(ensures);
			ensuresSMT.append(") ");
		}else{	
			ensuresSMT.append(ensures);
		}
		postNumber++;
		postCon.add(ensuresSMT.toString());
		
		combine ();
		
		return null;
	}
	
	@Override public String visitOldExpr(SimpleCParser.OldExprContext ctx) { 
	
		int varCount = variCount.get(ctx.getChild(2).getText()).get(1);
		if(varCount == 0){
		
			return ctx.getChild(2).getText() + "0"; 
		}else{
			return ctx.getChild(2).getText() + (varCount - 1);
		}
	}
	@Override 
	public String visitResultExpr(ResultExprContext ctx) {
		
		return returnExp;
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
		
	//	System.out.println("fde" + resSmt.toString());
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
						tempSmt.insert(tempSmt.length() - 1, res);
						resSmt.insert(resSmt.length() - i + 1, " " + tempSmt);
					}
					else {
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
						tempSmt.append("(bv2int (bvlshr )");
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
		if (getSubscript(var) > 0) {
			var += getSubscript(var) - 1;
		} else {
			var += getSubscript(var);
		}
		return var;
	}
	
	/** Get current subscripte for a specific variable **/
	private int getSubscript(String text) {
		return variCount.get(text).get(1);
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

}
