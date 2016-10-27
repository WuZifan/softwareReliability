package parser;

import parser.SimpleCParser.*;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.tree.ParseTree;


public class PreConditionVisitor extends SimpleCBaseVisitor<String> {

	private Map<String, ArrayList<Integer>> variCount;
	private StringBuilder smtResult = new StringBuilder();
	private ArrayList<String> preCon = new ArrayList<String>();
	
	private int preNumber = 0;

	public PreConditionVisitor(VariCount variCount){		
		
		this.variCount = variCount.getVarCount(); 	
		
	}
	
	public String getSMT(){
		
		return smtResult.toString();
		
	}
	
	public void combine (){
		
		if(preCon.isEmpty()){
			preCon.add("null");
		}
		
		smtResult = new StringBuilder();
		
		for(int i =0 ; i< preNumber-1; i++){
			smtResult.append(" (and ");
		}
		
		smtResult.append(preCon.get(0));
		
		for(int i =1 ; i< preNumber; i++){
			smtResult.append(preCon.get(i) + ") ");
		}
		
	}
	
	@Override
	public String visitPrepost (SimpleCParser.PrepostContext ctx){		
				
		super.visitPrepost(ctx);	
		
		combine ();
		System.out.println("pre::"+smtResult);
		
		return null;
	}	
	
	
	@Override
	public String visitRequires (SimpleCParser.RequiresContext ctx){
	
		String requires;	
		requires = super.visitRequires(ctx);
		
		preNumber++;
		preCon.add(requires);
		//System.out.print(preNumber+" "+"preCon::");
		
		return null;
	}	
	
	@Override
	public String visitAddExpr(AddExprContext ctx) {
		/*
		 *		注意，没有操作符，就没有操作数 
		 */
		StringBuilder result=new StringBuilder();
		List<String> opsList=new ArrayList<String>();
		for(Token token:ctx.ops){
			opsList.add(token.getText());
		}
		// Get the arg from super
		if(opsList.isEmpty()){
			return this.visitMulExpr((MulExprContext)ctx.getChild(0));
		}else{
			for(int i=0;i<opsList.size();i++){
				result.append("("+opsList.get(i)+" "+this.visitMulExpr(ctx.args.get(i))+" ");
			}
			result.append(" "+this.visitMulExpr(ctx.args.get(ctx.args.size()-1))+" ");
			for(int i=0; i<opsList.size();i++){
				result.append(") ");
			}
		}
		return result.toString();
	}
	
	@Override
	public String visitMulExpr(MulExprContext ctx) {
		StringBuilder result=new StringBuilder();
		List<String> opsList=new ArrayList<String>();
		for(Token token:ctx.ops){
			opsList.add(token.getText());
		}
		// Get the arg from super
		if(opsList.isEmpty()){
			return this.visitUnaryExpr((UnaryExprContext)ctx.getChild(0));
		}else{
			for(int i=0;i<opsList.size();i++){
				result.append("("+opsList.get(i)+" "+this.visitUnaryExpr(ctx.args.get(i))+" ");
			}
			result.append(" "+this.visitUnaryExpr(ctx.args.get(ctx.args.size()-1))+" ");
			for(int i=0; i<opsList.size();i++){
				result.append(") ");
			}
		}
		return result.toString();
	}
	
	@Override
	public String visitUnaryExpr(UnaryExprContext ctx) {
		StringBuilder result=new StringBuilder();
		List<String> opsList=new ArrayList<String>();
		for(Token token:ctx.ops){
			opsList.add(token.getText());
		}
		if(opsList.isEmpty()){
			return this.visitAtomExpr((AtomExprContext)ctx.getChild(0));
		}else{
			for(int i=0;i<opsList.size();i++){
				result.append("("+opsList.get(i)+" ");
			}
			result.append(" "+this.visitAtomExpr(ctx.arg)+" ");
			for(int i=0;i<opsList.size();i++){
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
	public String visitVarrefExpr(VarrefExprContext ctx) {
		
		return ctx.getText() + variCount.get(ctx.getText()).get(1);
	}
	
	@Override
	public String visitExpr(ExprContext ctx) {
		String resSmt;
		resSmt = super.visitExpr(ctx);
//		System.out.println("expr is " + resSmt + "  " + ctx.getText());
		return resSmt;
	}
	
	@Override
	public String visitTernExpr(TernExprContext ctx) {
		StringBuilder resSmt = new StringBuilder("");
		LorExprContext single = ctx.single;		
		String res;
		
		if (single != null) {
			//System.out.println(single.getText());
			resSmt.append(visitLorExpr(single));
		}
		else {
			resSmt.append("(ite )");
			Iterator<LorExprContext> iter = ctx.args.iterator();
			while(iter.hasNext()) {
				LorExprContext temp;
				temp = iter.next();
				System.out.println("dealing " + temp.getText());
				res = visitLorExpr(temp);
//				System.out.println("res " + res + "   " + ctx.getText());
				resSmt.insert(resSmt.length() - 1, res);
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
			while(iter.hasNext()) {
				StringBuilder tempSmt = new StringBuilder("");
				LandExprContext temp;
				
				if (i < ctx.ops.size()) {
					tempSmt.append("(or )");
					i++;
				}
				
				temp = iter.next();
				System.out.println("dealing " + temp.getText());
				res = visitLandExpr(temp);
				if (tempSmt.length() == 0) {
					resSmt.insert(resSmt.length() - i, " " + res);
				}
				else {
					tempSmt.insert(tempSmt.length() - 1, res);
					resSmt.insert(resSmt.length() - i + 1, " " + tempSmt);
				}
				
			}
		}
		
		//System.out.println("result " + resSmt.toString());
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
			while(iter.hasNext()) {
				StringBuilder tempSmt = new StringBuilder("");
				BorExprContext temp;
				
				if (i < ctx.ops.size()) {
					tempSmt.append("((and )");
					i++;
				}
				
				temp = iter.next();
				System.out.println("dealing " + temp.getText());
				res = visitBorExpr(temp);
				if (tempSmt.length() == 0) {
					resSmt.insert(resSmt.length() - i, " " + res);
				}
				else {
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
			while(iter.hasNext()) {
				StringBuilder tempSmt = new StringBuilder("");
				BxorExprContext temp;
				
				if (i < ctx.ops.size()) {
					tempSmt.append("(| )");
					i++;
				}
				
				temp = iter.next();
				System.out.println("dealing " + temp.getText());
				res = visitBxorExpr(temp);
				if (tempSmt.length() == 0) {
					resSmt.insert(resSmt.length() - i, " " + res);
				}
				else {
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
			while(iter.hasNext()) {
				StringBuilder tempSmt = new StringBuilder("");
				BandExprContext temp;
				
				if (i < ctx.ops.size()) {
					tempSmt.append("(^ )");
					i++;
				}
				
				temp = iter.next();
				System.out.println("dealing " + temp.getText());
				res = visitBandExpr(temp);
				if (tempSmt.length() == 0) {
					resSmt.insert(resSmt.length() - i, " " + res);
				}
				else {
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
			while(iter.hasNext()) {
				StringBuilder tempSmt = new StringBuilder("");
				EqualityExprContext temp;
				
				if (i < ctx.ops.size()) {
					tempSmt.append("(& )");
					i++;
				}
				
				temp = iter.next();
				System.out.println("dealing " + temp.getText());
				res = visitEqualityExpr(temp);
				if (tempSmt.length() == 0) {
					resSmt.insert(resSmt.length() - i, " " + res);
				}
				else {
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
			while(iter.hasNext()) {
				StringBuilder tempSmt = new StringBuilder("");
				RelExprContext temp;
				
				if (i < ctx.ops.size()) {
					
					if(ctx.ops.get(i).equals("==")){
						tempSmt.append("(= )");
					}else{
						tempSmt.append("(not )");
					}
					
					i++;
				}
				
				temp = iter.next();
				System.out.println("dealing " + temp.getText());
				res = visitRelExpr(temp);
				if (tempSmt.length() == 0) {
					resSmt.insert(resSmt.length() - i, " " + res);
				}
				else {
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
			while(iter.hasNext()) {
				StringBuilder tempSmt = new StringBuilder("");
				ShiftExprContext temp;
				
				if (i < ctx.ops.size()) {						
					tempSmt.append("(" + ctx.ops.get(i).getText() + " )");					
					i++;
				}
				
				temp = iter.next();
				System.out.println("dealing " + temp.getText());
				res = visitShiftExpr(temp);
				if (tempSmt.length() == 0) {
					resSmt.insert(resSmt.length() - i, " " + res);
				}
				else {
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
		}
		else {

			Iterator<AddExprContext> iter = ctx.args.iterator();
			int i = 0;
			while(iter.hasNext()) {
				StringBuilder tempSmt = new StringBuilder("");
				AddExprContext temp;
				
				if (i < ctx.ops.size()) {
					
					if(ctx.ops.get(i).equals(">>")){
						tempSmt.append("(bvlsh )");
					}else{
						tempSmt.append("(bvrshl )");
					}
					
					i++;
				}
				
				temp = iter.next();
				System.out.println("dealing " + temp.getText());
				res = visitAddExpr(temp);
				if (tempSmt.length() == 0) {
					resSmt.insert(resSmt.length() - i, " " + res);
				}
				else {
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
	public String visitParenExpr(ParenExprContext ctx) {
		String res = super.visitExpr(ctx.arg);
		return res;
	}
	
}
