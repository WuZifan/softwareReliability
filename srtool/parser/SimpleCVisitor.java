// Generated from SimpleC.g by ANTLR 4.5.3
package parser;
import org.antlr.v4.runtime.tree.ParseTreeVisitor;

/**
 * This interface defines a complete generic visitor for a parse tree produced
 * by {@link SimpleCParser}.
 *
 * @param <T> The return type of the visit operation. Use {@link Void} for
 * operations with no return type.
 */
public interface SimpleCVisitor<T> extends ParseTreeVisitor<T> {
	/**
	 * Visit a parse tree produced by {@link SimpleCParser#program}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitProgram(SimpleCParser.ProgramContext ctx);
	/**
	 * Visit a parse tree produced by {@link SimpleCParser#varDecl}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitVarDecl(SimpleCParser.VarDeclContext ctx);
	/**
	 * Visit a parse tree produced by {@link SimpleCParser#procedureDecl}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitProcedureDecl(SimpleCParser.ProcedureDeclContext ctx);
	/**
	 * Visit a parse tree produced by {@link SimpleCParser#formalParam}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFormalParam(SimpleCParser.FormalParamContext ctx);
	/**
	 * Visit a parse tree produced by {@link SimpleCParser#prepost}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitPrepost(SimpleCParser.PrepostContext ctx);
	/**
	 * Visit a parse tree produced by {@link SimpleCParser#requires}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitRequires(SimpleCParser.RequiresContext ctx);
	/**
	 * Visit a parse tree produced by {@link SimpleCParser#ensures}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitEnsures(SimpleCParser.EnsuresContext ctx);
	/**
	 * Visit a parse tree produced by {@link SimpleCParser#stmt}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitStmt(SimpleCParser.StmtContext ctx);
	/**
	 * Visit a parse tree produced by {@link SimpleCParser#assignStmt}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAssignStmt(SimpleCParser.AssignStmtContext ctx);
	/**
	 * Visit a parse tree produced by {@link SimpleCParser#assertStmt}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAssertStmt(SimpleCParser.AssertStmtContext ctx);
	/**
	 * Visit a parse tree produced by {@link SimpleCParser#assumeStmt}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAssumeStmt(SimpleCParser.AssumeStmtContext ctx);
	/**
	 * Visit a parse tree produced by {@link SimpleCParser#havocStmt}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitHavocStmt(SimpleCParser.HavocStmtContext ctx);
	/**
	 * Visit a parse tree produced by {@link SimpleCParser#callStmt}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCallStmt(SimpleCParser.CallStmtContext ctx);
	/**
	 * Visit a parse tree produced by {@link SimpleCParser#ifStmt}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIfStmt(SimpleCParser.IfStmtContext ctx);
	/**
	 * Visit a parse tree produced by {@link SimpleCParser#whileStmt}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitWhileStmt(SimpleCParser.WhileStmtContext ctx);
	/**
	 * Visit a parse tree produced by {@link SimpleCParser#blockStmt}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBlockStmt(SimpleCParser.BlockStmtContext ctx);
	/**
	 * Visit a parse tree produced by {@link SimpleCParser#loopInvariant}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitLoopInvariant(SimpleCParser.LoopInvariantContext ctx);
	/**
	 * Visit a parse tree produced by {@link SimpleCParser#invariant}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitInvariant(SimpleCParser.InvariantContext ctx);
	/**
	 * Visit a parse tree produced by {@link SimpleCParser#candidateInvariant}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCandidateInvariant(SimpleCParser.CandidateInvariantContext ctx);
	/**
	 * Visit a parse tree produced by {@link SimpleCParser#expr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitExpr(SimpleCParser.ExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link SimpleCParser#ternExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTernExpr(SimpleCParser.TernExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link SimpleCParser#lorExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitLorExpr(SimpleCParser.LorExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link SimpleCParser#landExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitLandExpr(SimpleCParser.LandExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link SimpleCParser#borExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBorExpr(SimpleCParser.BorExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link SimpleCParser#bxorExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBxorExpr(SimpleCParser.BxorExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link SimpleCParser#bandExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBandExpr(SimpleCParser.BandExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link SimpleCParser#equalityExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitEqualityExpr(SimpleCParser.EqualityExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link SimpleCParser#relExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitRelExpr(SimpleCParser.RelExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link SimpleCParser#shiftExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitShiftExpr(SimpleCParser.ShiftExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link SimpleCParser#addExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAddExpr(SimpleCParser.AddExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link SimpleCParser#mulExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitMulExpr(SimpleCParser.MulExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link SimpleCParser#unaryExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitUnaryExpr(SimpleCParser.UnaryExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link SimpleCParser#atomExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAtomExpr(SimpleCParser.AtomExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link SimpleCParser#numberExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitNumberExpr(SimpleCParser.NumberExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link SimpleCParser#varrefExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitVarrefExpr(SimpleCParser.VarrefExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link SimpleCParser#parenExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitParenExpr(SimpleCParser.ParenExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link SimpleCParser#resultExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitResultExpr(SimpleCParser.ResultExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link SimpleCParser#oldExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitOldExpr(SimpleCParser.OldExprContext ctx);
}