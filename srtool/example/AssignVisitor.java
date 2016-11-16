package example;

import java.util.ArrayList;
import java.util.List;
import java.util.Stack;

import org.antlr.v4.parse.ANTLRParser.exceptionGroup_return;
import org.antlr.v4.runtime.Token;

import parser.SimpleCBaseVisitor;
import parser.SimpleCParser.AddExprContext;
import parser.SimpleCParser.AssignStmtContext;
import parser.SimpleCParser.AtomExprContext;
import parser.SimpleCParser.ExprContext;
import parser.SimpleCParser.MulExprContext;
import parser.SimpleCParser.NumberExprContext;
import parser.SimpleCParser.ParenExprContext;
import parser.SimpleCParser.UnaryExprContext;
import parser.SimpleCParser.VarrefExprContext;

public class AssignVisitor  extends SimpleCBaseVisitor<String>{
		
	@Override
	public String visitAssignStmt(AssignStmtContext ctx) {
		String result=this.visitExpr((ExprContext)ctx.getChild(2));
		System.out.println(result);
		return result;
	}
	
	@Override
	public String visitExpr(ExprContext ctx) {
		String result=super.visitExpr(ctx);
		return result;
	}
	
	@Override
	public String visitAddExpr(AddExprContext ctx) {
		/*
		 *		
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
				result.append("("+opsList.get(i)+this.visitMulExpr(ctx.args.get(i))+" ");
			}
			result.append(this.visitMulExpr(ctx.args.get(ctx.args.size()-1)));
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
				result.append("("+opsList.get(i)+this.visitUnaryExpr(ctx.args.get(i))+" ");
			}
			result.append(this.visitUnaryExpr(ctx.args.get(ctx.args.size()-1)));
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
			result.append(this.visitAtomExpr(ctx.arg));
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
	public String visitParenExpr(ParenExprContext ctx) {
		return this.visitExpr(ctx.arg);
	}
	
	@Override
	public String visitNumberExpr(NumberExprContext ctx) {
		return ctx.getText();
	}
	
	@Override
	public String visitVarrefExpr(VarrefExprContext ctx) {
		return ctx.getText();
	}

}
