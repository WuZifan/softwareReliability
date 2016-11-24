package tool;



import parser.GlobalVisitor;
import parser.MyAssertVisitor;
import parser.ParameterVisitor;
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
		this.result = new StringBuilder("(set-logic QF_IRA)\n");
		this.glVisitor = new GlobalVisitor(VarCount);
		this.paVisitor = new ParameterVisitor(VarCount);

		// You will probably find it useful to add more fields and
		// constructor arguments
	}
	

	public Void generateVCGlobal() {

		this.glVisitor.visit(prog);
		String res = this.glVisitor.getSMT().toString();
		VCGenerator.glSmt = res;
		return null;
	}

	@SuppressWarnings("unused")
	public StringBuilder generateVC() {
		String paRes;

		mav = new MyAssertVisitor();
		tv = new TestVisitor(mav, VarCount, VCGenerator.glSmt, null);

		tv.visit(this.prog);
		return result;
	}
	
	@SuppressWarnings("unused")
	private void getAssertNot(String postSMT){
		String mavSMT= mav.getUnAssSMT();
		
		if(postSMT.isEmpty()|| postSMT.equals("null")){
			if(mavSMT.isEmpty()){
				result.append("(assert false)");
			}else{
				result.append("(assert (not ");
				result.append(mavSMT);
				result.append("))");
			}			
		}else{
			if(mavSMT.isEmpty()){
				result.append("(assert (not ");
				result.append(postSMT);
				result.append("))");
			}else{
				result.append("(assert (not (and");
				result.append(postSMT);
				result.append(mavSMT);
				result.append(")))");
			}	
		}			
	}
}
