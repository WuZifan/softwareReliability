package tool;
import parser.GlobalVisitor;
import parser.SimpleCParser.ProcedureDeclContext;
import parser.SimpleCParser.ProgramContext;
import parser.MyAssertVisitor;
import parser.TestVisitor;
import parser.VariCount;

public class VCGenerator {
	private ProcedureDeclContext proc;
	private ProgramContext prog;
	private TestVisitor tv;
	private GlobalVisitor gl;
	private StringBuilder result;
	private VariCount VarCount;
	private MyAssertVisitor mav;
	private static String glSmt;
	
	public VCGenerator(ProgramContext prog, ProcedureDeclContext proc) {
		this.proc = proc;
		this.prog = prog;
		this.result = new StringBuilder("(set-logic QF_LIA)\n");
		this.VarCount = new VariCount();
		this.tv = new TestVisitor();
		this.gl = new GlobalVisitor(this.VarCount);
		
	
		// TODO: You will probably find it useful to add more fields and constructor arguments
	}
	
	public Void generateVCGlobal() {
		
		gl.visit(prog);
		String res = gl.getSMT().toString();
		VCGenerator.glSmt = res;
		return null;
	}
	
	public StringBuilder generateVC() {
//		StringBuilder result = new StringBuilder("(set-logic QF_BV)\n");
//		result.append("(set-option :produce-models true)\n");
//		result.append("(define-fun tobv32 ((p Bool)) (_ BitVec 32) (ite p (_ bv1 32) (_ bv0 32)))\n");
//		result.append("(define-fun tobool ((p (_ BitVec 32))) Bool (ite (= p (_ bv0 32)) false true))\n");

		mav = new MyAssertVisitor();
		tv = new TestVisitor(mav, this.VarCount, VCGenerator.glSmt);
		
		// assert分两种，
		// 赋值语句的assert要是对的才行
		// pre-/post- condition的条件全部写在一起，前面加not 条件之间关系为and
		tv.visit(proc);
		result.append(tv.getSMT());	
		result.append(mav.getAssSMT());
		// TODO: generate the meat of the VC
		result.append("\n(check-sat)\n");
		System.out.println(result.toString());
		return result;
	}

}
