package example;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;

import org.antlr.v4.runtime.Token;

import parser.SimpleCBaseVisitor;
import parser.SimpleCParser.AddExprContext;
import parser.SimpleCParser.AssertStmtContext;
import parser.SimpleCParser.AssignStmtContext;
import parser.SimpleCParser.ExprContext;
import parser.SimpleCParser.MulExprContext;
import parser.SimpleCParser.ParenExprContext;
import parser.SimpleCParser.UnaryExprContext;

public class Count42sVisitor2 extends SimpleCBaseVisitor<Void> {

	private int num42s = 0;
	private boolean inAssert = false;
	private Queue<String> oprQue = new LinkedList<String>();
	private Queue<String> argQue = new LinkedList<String>();
	private BTree root=new BTree();
	private Queue<BTree> btList=new LinkedList<BTree>();

	@Override
	public Void visitAssertStmt(AssertStmtContext ctx) {
		inAssert = true;
		super.visitAssertStmt(ctx);
		inAssert = false;
		return null;
	}

	@Override
	public Void visitExpr(ExprContext ctx) {
		return super.visitExpr(ctx);
	}

	@Override
	public Void visitAssignStmt(AssignStmtContext ctx) {
		for(int i=0;i<ctx.getChildCount();i++){
			System.out.println("ASS:  "+ctx.getChild(i).getText());
		}
		super.visitAssignStmt(ctx);
		System.out.println("BT SIZE:"+btList.size());
		return null;
	}
	
	@Override
	public Void visitAddExpr(AddExprContext ctx) {
		List<String> opsList=new ArrayList<String>();
		List<String> argList=new ArrayList<String>();
		for(Token token:ctx.ops){
			opsList.add(token.getText());
			System.out.println("add:"+token.getText());
		}
		for(MulExprContext mec:ctx.args){
			argList.add(mec.getText());
			System.out.println("add:"+mec.getText());
		}
		return super.visitAddExpr(ctx);
	}
	
	@Override
	public Void visitMulExpr(MulExprContext ctx) {

		return super.visitMulExpr(ctx);
	}
	
	@Override
	public Void visitUnaryExpr(UnaryExprContext ctx) {
		 super.visitUnaryExpr(ctx);
		if(ctx.arg!=null){
			String arg=ctx.arg.getText();
			if(!arg.contains("(")){
				System.out.println(arg);
				BTree argBT=new BTree(arg);
				BTree opsBT=null;
				for(Token token:ctx.ops){
					if(opsBT==null){
						opsBT=new BTree(token.getText());
					}else{
						BTree temp=new BTree(token.getText());
						BTree leftNode=opsBT;
						while(leftNode.getLeft()!=null){
							leftNode=leftNode.getLeft();
						}
						leftNode.setLeft(temp);
					}
				}
				BTree leftNode=opsBT;
				while(leftNode.getLeft()!=null){
					leftNode=leftNode.getLeft();
				}
				leftNode.setLeft(argBT);
				this.btList.add(opsBT);
			}
		}
		
		for(int i=0;i<ctx.getChildCount();i++){
			System.out.println(ctx.getChild(i).getText());
		}
		return null;
	}

	/**
	 */
	@Override
	public Void visitParenExpr(ParenExprContext ctx) {
		System.out.println("lol");
		return super.visitParenExpr(ctx);
	}
	
	private Void frontFirstFind(BTree root){
		if(root.getValue()!=null){
			System.out.println(root.getValue());
			if(root.getLeft()!=null){
				frontFirstFind(root.getLeft());
			}
			if(root.getRight()!=null){
				frontFirstFind(root.getRight());
			}
		}
	
		return null;
	}
	
}	

class BTree{
	private String value=null;
	private BTree left=null;
	private BTree right=null;
	public BTree() {
	}
	
	public BTree(String value){
		this.value=value;
	}

	public String getValue() {
		return value;
	}

	public void setValue(String value) {
		this.value = value;
	}

	public BTree getLeft() {
		return left;
	}

	public void setLeft(BTree left) {
		this.left = left;
	}

	public BTree getRight() {
		return right;
	}

	public void setRight(BTree right) {
		this.right = right;
	}
}
