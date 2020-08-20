package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.smt.SolverCommunication.Message;
import de.uka.ilkd.key.smt.SolverCommunication.MessageType;

import java.io.IOException;

/**
 * The SolverSocket class describes the communication between the KeY and the SMT solver processe.
 * This description is no longer part of the SolverType because in the case when we search for counterexamples
 * and one is found, the model has to be queried. This query depends on the SMT problem and is not the same for 
 * all solvers of a given type.  
 * @author mihai
 *
 */
public abstract class AbstractSolverSocket {
	protected static final int WAIT_FOR_RESULT = 0;
	protected static final int WAIT_FOR_DETAILS =1;
	protected static final int WAIT_FOR_QUERY = 2;
	protected static final int WAIT_FOR_MODEL = 3;
	protected static final int FINISH = 4;

    static final String UNKNOWN = "unknown";
    static final String SAT = "sat";
    static final String UNSAT = "unsat";
	
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

	public abstract void messageIncoming(Pipe<SolverCommunication> pipe, Message message) throws IOException;

	public static AbstractSolverSocket createSocket(SolverType type, ModelExtractor query){
		String name = type.getName();
		if(type == SolverType.Z3_SOLVER){
			return new Z3Socket(name, query);
		}
		else if(type == SolverType.Z3_CE_SOLVER){
			return new Z3CESocket(name, query);
		}
		else if(type == SolverType.Z3_NEW_TL_SOLVER){
			return new Z3Socket(name, query);
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
        else if(type == SolverType.CVC4_SOLVER){
            return new CVC4Socket(name, query);
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

	public void messageIncoming(Pipe<SolverCommunication> pipe, Message message) throws IOException {
		SolverCommunication sc = pipe.getSession();
		String msg = message.getContent().trim();
		if(message.getType() == MessageType.Error || msg.startsWith("(error")) {
			sc.addMessage(msg);
			if(msg.indexOf("WARNING:")>-1){
				return;
			}
			throw new IOException("Error while executing Z3: " + msg);
		}

		if (!msg.equals("success")) {
			sc.addMessage(msg);
		}

		switch (sc.getState()) {
			case WAIT_FOR_RESULT:
				if(msg.equals("unsat")){
					sc.setFinalResult(SMTSolverResult.createValidResult(name));
					// One cannot ask for proofs and models at one time
					// rather have modesl than proofs (MU, 2013-07-19)
					// pipe.sendMessage("(get-proof)\n");
					pipe.sendMessage("(exit)");
					sc.setState(WAIT_FOR_DETAILS);
				}
				if(msg.equals("sat")){
					sc.setFinalResult(SMTSolverResult.createInvalidResult(name));
					pipe.sendMessage("(get-model)");
					pipe.sendMessage("(exit)");
					sc.setState(WAIT_FOR_DETAILS);

				}
				if(msg.equals("unknown")){
					sc.setFinalResult(SMTSolverResult.createUnknownResult(name));
					sc.setState(WAIT_FOR_DETAILS);
					pipe.sendMessage("(exit)\n");
				}
				break;

			case WAIT_FOR_DETAILS:
				if(msg.equals("success")){
					pipe.close();
				}
				break;
		}
	}

}

class Z3CESocket extends AbstractSolverSocket{

	public Z3CESocket(String name, ModelExtractor query) {
		super(name, query);
	}



	@Override
	public void messageIncoming(Pipe<SolverCommunication> pipe, Message message) throws IOException {
		SolverCommunication sc = pipe.getSession();
		String msg = message.getContent().trim();

		if(message.getType() == MessageType.Error || msg.startsWith("(error")) {
			sc.addMessage(msg);
			if(msg.indexOf("WARNING:")>-1){
				return;
			}
			throw new IOException("Error while executing Z3: " +msg);
		}
		if (!msg.equals("success")) {
			sc.addMessage(msg);
		}

		switch (sc.getState()) {
			case WAIT_FOR_RESULT:
				if(msg.equals("unsat")){
					sc.setFinalResult(SMTSolverResult.createValidResult(name));
					//pipe.sendMessage("(get-proof)\n");
					pipe.sendMessage("(exit)");
					sc.setState(WAIT_FOR_DETAILS);
				}
				if(msg.equals("sat")){
					sc.setFinalResult(SMTSolverResult.createInvalidResult(name));
					pipe.sendMessage("(get-model)");
					pipe.sendMessage("(echo \"endmodel\")");
					sc.setState(WAIT_FOR_MODEL);					
				}
				if(msg.equals("unknown")){
					sc.setFinalResult(SMTSolverResult.createUnknownResult(name));
					sc.setState(WAIT_FOR_DETAILS);
					pipe.sendMessage("(exit)");
				}

				break;

			case WAIT_FOR_DETAILS:
				if(msg.equals("success")){
					pipe.close();
				}						
				break;		

			case WAIT_FOR_QUERY:
				if(msg.equals("success")){
					pipe.close();
				}
				else {
					query.messageIncoming(pipe, msg, message.getType().ordinal());
				}

				break;

			case WAIT_FOR_MODEL:
				if(msg.equals("endmodel")){
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

	public void messageIncoming(Pipe<SolverCommunication> pipe, Message message) throws IOException {
		SolverCommunication sc = pipe.getSession();
		String msg = message.getContent().replace('-', ' ').trim();
		sc.addMessage(msg);
		if(message.getType() == MessageType.Error && msg.indexOf("Interrupted by signal") == -1) {
			throw new IOException("Error while executing CVC3: " + msg);
		}

		if(sc.getState() == WAIT_FOR_RESULT ){
			if(msg.indexOf("unsat") > -1){
				sc.setFinalResult(SMTSolverResult.createValidResult(name));
			} else if(msg.indexOf("sat") > -1){
				sc.setFinalResult(SMTSolverResult.createInvalidResult(name));
			}
			sc.setState(FINISH);
			pipe.close();
		}

	}

}

class CVC4Socket extends AbstractSolverSocket{


    public CVC4Socket(String name, ModelExtractor query) {
        super(name, query);
    }

	public void messageIncoming(Pipe<SolverCommunication> pipe, Message message) throws IOException {
        SolverCommunication sc = pipe.getSession();
		String msg = message.getContent().trim();
        if ("".equals(msg)) return;
        if (msg.indexOf("success")==-1)
            sc.addMessage(msg);
        if (message.getType() == MessageType.Error) {
            throw new IOException("Error while executing CVC4: " +msg);
        }

        // temp hack TODO js/mu
		if(msg.contains("(error ")) {
			throw new IOException("Something went wrong somewhere in CVC4: " + msg);
		}

        if(sc.getState() == WAIT_FOR_RESULT ){
            if(msg.indexOf("\n"+UNSAT) > -1){
                sc.setFinalResult(SMTSolverResult.createValidResult(name));
                sc.setState(FINISH);
                pipe.close();
            } else if(msg.indexOf("\n"+SAT) > -1){
                sc.setFinalResult(SMTSolverResult.createInvalidResult(name));
                sc.setState(FINISH);
                pipe.close();
            } else if(msg.indexOf("\n"+UNKNOWN)> -1){
                sc.setFinalResult(SMTSolverResult.createUnknownResult(name));
                sc.setState(FINISH);
                pipe.close();
            }
        }

    }

}
class SimplifySocket extends AbstractSolverSocket{

	public SimplifySocket(String name, ModelExtractor query) {
		super(name, query);
	}

	@Override
	public void messageIncoming(Pipe<SolverCommunication> pipe, Message message) {
		SolverCommunication sc = pipe.getSession();
		sc.addMessage(message.getContent());


		if(message.getContent().indexOf("Valid.")>-1){
			sc.setFinalResult(SMTSolverResult.createValidResult(name));						
			pipe.close();
		}

		if(message.getContent().indexOf("Invalid.")>-1){
			sc.setFinalResult(SMTSolverResult.createInvalidResult(name));						 
			pipe.close();
		}

		if(message.getContent().indexOf("Bad input:")>-1){
			pipe.close();
		}
	}	
}

class YICESSocket extends AbstractSolverSocket{

	public YICESSocket(String name, ModelExtractor query) {
		super(name, query);
	}

	@Override
	public void messageIncoming(Pipe<SolverCommunication> pipe, Message message) {
		SolverCommunication sc = pipe.getSession();
		String msg = message.getContent().replaceAll("\n","");
		sc.addMessage(msg);


		if(msg.equals(UNSAT)) {
			sc.setFinalResult(SMTSolverResult.createValidResult(name));						
			pipe.close();
		}

		if(msg.equals(SAT)) {
			sc.setFinalResult(SMTSolverResult.createInvalidResult(name));						 
			pipe.close();
		}
	}

}




