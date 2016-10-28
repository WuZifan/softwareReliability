package tool;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import parser.GlobalVisitor;
import parser.MyAssertVisitor;
import parser.ParameterVisitor;
import parser.PostConditionVisitor;
import parser.PreConditionVisitor;
import parser.SimpleCParser.ProcedureDeclContext;
import parser.SimpleCParser.ProgramContext;
import parser.TestVisitor;
import parser.VariCount;

public class VCGenerator {
	private ProcedureDeclContext proc;
	private ProgramContext prog;
	private TestVisitor tv;
	private GlobalVisitor glVisitor;
	private ParameterVisitor paVisitor;
	private StringBuilder result;
	private static VariCount VarCount;
	private MyAssertVisitor mav;
	private static String glSmt;
	static {
		VarCount = new VariCount();
	}

	public VCGenerator(ProgramContext prog, ProcedureDeclContext proc) {
		this.proc = proc;
		this.prog = prog;
		// this.result = new StringBuilder("(set-logic QF_LIA)\n");
		this.result = new StringBuilder("(set-logic QF_IRA)\n");
		this.glVisitor = new GlobalVisitor(VarCount);
		this.paVisitor = new ParameterVisitor(VarCount);

		// TODO: You will probably find it useful to add more fields and
		// constructor arguments
	}

	public Void generateVCGlobal() {

		this.glVisitor.visit(prog);
		String res = this.glVisitor.getSMT().toString();
		VCGenerator.glSmt = res;
		return null;
	}

	public StringBuilder generateVC() {
		// StringBuilder result = new StringBuilder("(set-logic QF_BV)\n");
		// result.append("(set-option :produce-models true)\n");
		// result.append("(define-fun tobv32 ((p Bool)) (_ BitVec 32) (ite p (_
		// bv1 32) (_ bv0 32)))\n");
		// result.append("(define-fun tobool ((p (_ BitVec 32))) Bool (ite (= p
		// (_ bv0 32)) false true))\n");

		String paRes;
		this.paVisitor.visit(proc);
		paRes = this.paVisitor.getSMT().toString();

		mav = new MyAssertVisitor();
		tv = new TestVisitor(mav, VarCount, VCGenerator.glSmt, paRes);

		// assert分两种，
		// 赋值语句的assert要是对的才行
		// pre-/post- condition的条件全部写在一起，前面加not 条件之间关系为and
		tv.visit(proc);
		// 拼接函数声明语句
		result.append(getDivFunSMT());

		result.append(getInttoBoolSmt());
		result.append(getBooltoIntSmt());
		System.out.println("FunDecl: \n" + getDivFunSMT());
		// 拼接新增下标后的声明语句
		result.append(getDeclSMTofRest());
		System.out.println("DeclSMT: \n" + getDeclSMTofRest());
		// 拼接TestVisitor里面的SMT
		result.append(tv.getSMT());
		System.out.println("TVSMT: \n" + tv.getSMT());
		// 拼接assert语句
		//////////////////////////////////////////////////////////////////////
		result.append(mav.getAssSMT());
		System.out.println("MavSMT: \n" + mav.getAssSMT());
		
		PreConditionVisitor preVisitor = new PreConditionVisitor(VarCount);
		preVisitor.visit(proc);
		PostConditionVisitor postVisitor = new PostConditionVisitor(preVisitor.getSMT(),VarCount);
		postVisitor.visit(proc);
		getAssertNot(preVisitor.getSMT(),postVisitor.getSMT());
		
		//////////////////////////////////////////////////////////////////////
		// TODO: generate the meat of the VC
		result.append("\n(check-sat)\n");
		// result.append("\n(check-sat-using qfnra-nlsat)\n");
		 System.out.println("FinalResult:-------------------------------\n"+result.toString());
		return result;
	}
	
	private void getAssertNot(String preSMT,String postSMT){
		if(postSMT.isEmpty()){
//			result.append("(assert false)");
		}else{
			result.append("(assert (not ");
			result.append(postSMT);
			result.append("))");
		}			
	}

	private String getDivFunSMT() {
		StringBuilder result = new StringBuilder();
		result.append("(define-fun mydiv ((x Int) (y Int)) Int\n" + "(ite (= y 0) x (div x y)))\n");
		result.append("(define-fun mymod ((x Int) (y Int)) Int\n" + "(ite (= y 0) x (mod x y)))\n");
		// TODO Test assume
		return result.toString();
	}
	
	private String getInttoBoolSmt() {
		StringBuilder result = new StringBuilder();
		result.append("(define-fun itb ((x Int)) Bool\n");
		result.append("(ite (= x 0) false true))\n");
		return result.toString();
	}
	
	private String getBooltoIntSmt() {
		StringBuilder result = new StringBuilder();
		result.append("(define-fun bti ((x Bool)) Int\n");
		result.append("(ite (= x true) 1 0))\n");
		return result.toString();
	}

	private String getDeclSMTofRest() {
		StringBuilder re = new StringBuilder();
		// 拼接新增下标后的声明语句
		Map<String, ArrayList<Integer>> decMap = VarCount.getVarCount();
		for (String key : decMap.keySet()) {
			List<Integer> varList = decMap.get(key);
			if (varList.get(1) == 0) {
				re.append("(declare-fun ");
				re.append(key + 0 + " ");
				re.append("() ");
				re.append("Int" + ")");
				re.append("\n");
			} else {
				for (int i = 0; i <1+ varList.get(1); i++) {
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
}
