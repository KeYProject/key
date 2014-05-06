package de.uka.ilkd.key.smt;

/**
 * The SolverSocket class describes the communication between the KeY and the SMT solver processe.
 * This description is no longer part of the SolverType because in the case when we search for counterexamples
 * and one is found, the model has to be queried. This query depends on the SMT problem and is not the same for 
 * all solvers of a given type.  
 * @author mihai
 *
 */
public abstract class AbstractSolverSocket implements PipeListener<SolverCommunication> {
	protected static final int WAIT_FOR_RESULT = 0;
	protected static final int WAIT_FOR_DETAILS =1;
	protected static final int WAIT_FOR_QUERY = 2;
	protected static final int WAIT_FOR_MODEL = 3;
	protected static final int FINISH = 4;

	protected String name;

	protected ModelExtractor query = null;

	public AbstractSolverSocket(String name, ModelExtractor query) {
		super();
		this.name = name;
		this.query = query;
	}
	
	public ModelExtractor getQuery(){
		return query;
	}

	@Override
	public void exceptionOccurred(Pipe<SolverCommunication> pipe,
			Throwable exception) {
		pipe.getSession().addException(exception);

	}

	public static AbstractSolverSocket createSocket(SolverType type, ModelExtractor query){
		String name = type.getName();
		if(type==SolverType.Z3_SOLVER){
			return new Z3Socket(name, query);
		}
		else if(type == SolverType.Z3_CE_SOLVER){
			return new Z3CESocket(name, query);
		}
		else if(type == SolverType.SIMPLIFY_SOLVER){
			return new SimplifySocket(name, query);
		}
		else if(type == SolverType.YICES_SOLVER){
			return new YICESSocket(name, query);
		}
		else if(type == SolverType.CVC3_SOLVER){
			return new CVC3Socket(name, query);
		}

		return null;
	}

	public void setQuery(ModelExtractor query) {
	    this.query = query;
	    
    }


}

class Z3Socket extends AbstractSolverSocket{

	public Z3Socket(String name, ModelExtractor query) {
		super(name, query);	    
	}

	public void messageIncoming(Pipe<SolverCommunication> pipe, String message, int type) {
		SolverCommunication sc = pipe.getSession();
		if(type == Pipe.ERROR_MESSAGE || message.startsWith("(error")){
			sc.addMessage(message);
			if(message.indexOf("WARNING:")>-1){
				return;
			}
			throw new RuntimeException("Error while executing Z3:\n" +message);
		}
		if (!message.equals("success")) {
			sc.addMessage(message);
		}

		switch (sc.getState()) {
			case WAIT_FOR_RESULT:
				if(message.equals("unsat")){
					sc.setFinalResult(SMTSolverResult.createValidResult(name));
					// One cannot ask for proofs and models at one time
					// rather have modesl than proofs (MU, 2013-07-19)
					// pipe.sendMessage("(get-proof)\n");
					pipe.sendMessage("(exit)\n");
					sc.setState(WAIT_FOR_DETAILS);
				}
				if(message.equals("sat")){
					sc.setFinalResult(SMTSolverResult.createInvalidResult(name));
					pipe.sendMessage("(get-model)");
					pipe.sendMessage("(exit)\n");
					sc.setState(WAIT_FOR_DETAILS);

				}
				if(message.equals("unknown")){
					sc.setFinalResult(SMTSolverResult.createUnknownResult(name));
					sc.setState(WAIT_FOR_DETAILS);
					pipe.sendMessage("(exit)\n");
				}
				break;

			case WAIT_FOR_DETAILS:
				if(message.equals("success")){
					pipe.close();
				}
				break;
		}
	}

	@Override
	public void exceptionOccurred(Pipe<SolverCommunication> pipe,
			Throwable exception) {


	}

}

class Z3CESocket extends AbstractSolverSocket{

	public Z3CESocket(String name, ModelExtractor query) {
		super(name, query);
	}



	@Override
	public void messageIncoming(Pipe<SolverCommunication> pipe, String message,
			int type) {

		SolverCommunication sc = pipe.getSession();
		if(type == Pipe.ERROR_MESSAGE || message.startsWith("(error")){
			sc.addMessage(message);
			if(message.indexOf("WARNING:")>-1){
				return;
			}
			throw new RuntimeException("Error while executing Z3:\n" +message);
		}
		if (!message.equals("success")) {
			sc.addMessage(message);
		}

		switch (sc.getState()) {
			case WAIT_FOR_RESULT:
				if(message.equals("unsat")){
					sc.setFinalResult(SMTSolverResult.createValidResult(name));
					//pipe.sendMessage("(get-proof)\n");
					pipe.sendMessage("(exit)\n");
					sc.setState(WAIT_FOR_DETAILS);
				}
				if(message.equals("sat")){
					sc.setFinalResult(SMTSolverResult.createInvalidResult(name));
					pipe.sendMessage("(get-model)");
					pipe.sendMessage("(echo \"endmodel\")");
					sc.setState(WAIT_FOR_MODEL);					
				}
				if(message.equals("unknown")){
					sc.setFinalResult(SMTSolverResult.createUnknownResult(name));
					sc.setState(WAIT_FOR_DETAILS);
					pipe.sendMessage("(exit)\n");
				}

				break;

			case WAIT_FOR_DETAILS:
				if(message.equals("success")){
					pipe.close();
				}						
				break;		

			case WAIT_FOR_QUERY:
				if(message.equals("success")){
					pipe.close();
				}
				else{
					query.messageIncoming(pipe, message, type);
				}

				break;

			case WAIT_FOR_MODEL:
				if(message.equals("endmodel")){
					if(query !=null && query.getState()==ModelExtractor.DEFAULT){
						query.getModel().setEmpty(false);
						//System.out.println("Starting query");						 
						query.start(pipe);
						sc.setState(WAIT_FOR_QUERY);
					}
					else{
						pipe.sendMessage("(exit)\n");
						sc.setState(WAIT_FOR_DETAILS); 
					}
				}


				break;
		}

	}


}

class CVC3Socket extends AbstractSolverSocket{

	public CVC3Socket(String name, ModelExtractor query) {
		super(name, query);
	}

	public void messageIncoming(Pipe<SolverCommunication> pipe, String message, int type) {
		SolverCommunication sc = pipe.getSession();
		sc.addMessage(message);
		if(type == Pipe.ERROR_MESSAGE && message.indexOf("Interrupted by signal")==-1){
			throw new RuntimeException("Error while executing CVC:\n" +message);
		}

		if(sc.getState() == WAIT_FOR_RESULT ){
			if(message.indexOf(" unsat") > -1){
				sc.setFinalResult(SMTSolverResult.createValidResult(name));
			} else if(message.indexOf("sat") > -1){
				sc.setFinalResult(SMTSolverResult.createInvalidResult(name));
			}
			sc.setState(FINISH);
			pipe.close();

		}

	}

}

class SimplifySocket extends AbstractSolverSocket{

	public SimplifySocket(String name, ModelExtractor query) {
		super(name, query);
	}

	@Override
	public void messageIncoming(Pipe<SolverCommunication> pipe,String message, int type) {
		SolverCommunication sc = pipe.getSession();
		sc.addMessage(message);		


		if(message.indexOf("Valid.")>-1){
			sc.setFinalResult(SMTSolverResult.createValidResult(name));						
			pipe.close();
		}

		if(message.indexOf("Invalid.")>-1){
			sc.setFinalResult(SMTSolverResult.createInvalidResult(name));						 
			pipe.close();
		}

		if(message.indexOf("Bad input:")>-1){
			pipe.close();
		}
	}	
}

class YICESSocket extends AbstractSolverSocket{

	public YICESSocket(String name, ModelExtractor query) {
		super(name, query);
	}

	@Override
	public void messageIncoming(Pipe<SolverCommunication> pipe, String message, int type) {
		SolverCommunication sc = pipe.getSession();
		message = message.replaceAll("\n","");
		sc.addMessage(message);		


		if(message.equals("unsat")){
			sc.setFinalResult(SMTSolverResult.createValidResult(name));						
			pipe.close();
		}

		if(message.equals("sat")){
			sc.setFinalResult(SMTSolverResult.createInvalidResult(name));						 
			pipe.close();
		}

	}

}




