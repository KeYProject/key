package de.uka.ilkd.key.smt.communication;

import de.uka.ilkd.key.smt.ModelExtractor;
import de.uka.ilkd.key.smt.SMTSolverResult;
import de.uka.ilkd.key.smt.SolverType;
import de.uka.ilkd.key.smt.communication.SolverCommunication.MessageType;

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

	public abstract void messageIncoming(Pipe pipe, String message) throws IOException;

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
        else if(type == SolverType.CVC4_SOLVER){
            return new CVC4Socket(name, query);
        }
        else if(type == SolverType.CVC4_NEW_TL_SOLVER){
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

	public void messageIncoming(Pipe pipe, String message) throws IOException {
		SolverCommunication sc = pipe.getSession();
		String msg = message; // do not trim (loses indentation) // .trim();
		if(msg.startsWith("(error")) {
			sc.addMessage(msg, MessageType.Error);
			if(msg.contains("WARNING:")){
				return;
			}
			throw new IOException("Error while executing Z3: " + msg);
		}

		// TODO: success messages should also occur in the raw solver output
		if (!msg.equals("success")) {
			sc.addMessage(msg, MessageType.Output);
		}

		switch (sc.getState()) {
			case WAIT_FOR_RESULT:
				if(msg.equals("unsat")){
					sc.setFinalResult(SMTSolverResult.createValidResult(name));
					// TODO: does not work with legacy Z3 translation, as proof production is not
					//  enabled there
					pipe.sendMessage("(get-proof)");
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
					pipe.sendMessage("(exit)\n");
					sc.setState(WAIT_FOR_DETAILS);
				}
				break;

			case WAIT_FOR_DETAILS:
				if(msg.equals("success")){
//					pipe.sendMessage("(exit)");
//					pipe.close();
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
	public void messageIncoming(Pipe pipe, String message) throws IOException {
		SolverCommunication sc = pipe.getSession();
		String msg = message.trim();

		if(msg.startsWith("(error")) {
			sc.addMessage(msg, MessageType.Error);
			if(msg.contains("WARNING:")){
				return;
			}
			throw new IOException("Error while executing Z3: " +msg);
		}
		// TODO: success messages should also occur in the raw solver output
		if (!msg.equals("success")) {
			sc.addMessage(msg, MessageType.Output);
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
//					pipe.close();
				}
				break;

			case WAIT_FOR_QUERY:
				if(msg.equals("success")){
//					pipe.close();
				}
				else {
					query.messageIncoming(pipe, msg);
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

class CVC4Socket extends AbstractSolverSocket{


    public CVC4Socket(String name, ModelExtractor query) {
        super(name, query);
    }

	public void messageIncoming(Pipe pipe, String message) throws IOException {
        SolverCommunication sc = pipe.getSession();
		String msg = message.trim();
        if ("".equals(msg)) return;
        if (!msg.contains("success"))
            sc.addMessage(msg, MessageType.Output);
        if (message.contains("error") || message.contains("Error")) {
            sc.addMessage(message, MessageType.Error);
            throw new IOException("Error while executing CVC4: " + msg);
		}

        if(sc.getState() == WAIT_FOR_RESULT ){
            if(msg.contains("\n" + UNSAT)){
                sc.setFinalResult(SMTSolverResult.createValidResult(name));
                sc.setState(FINISH);
				pipe.sendMessage("(exit)");
//				pipe.close();
			} else if(msg.contains("\n" + SAT)){
				sc.setFinalResult(SMTSolverResult.createInvalidResult(name));
				sc.setState(FINISH);
				pipe.sendMessage("(exit)");
//				pipe.close();
			} else if(msg.contains("\n" + UNKNOWN)){
				sc.setFinalResult(SMTSolverResult.createUnknownResult(name));
				sc.setState(FINISH);
                pipe.sendMessage("(exit)");
//                pipe.close();
            }
        }
    }
}
