package visualdebugger.views;

import org.eclipse.jdt.core.IProblemRequestor;
import org.eclipse.jdt.core.compiler.IProblem;

public class ProblemRequestor implements IProblemRequestor{

	private IProblem problem = null;
	
	public void acceptProblem(IProblem problem) {

		this.problem=problem;
						
	}

	public void beginReporting() {
		// TODO Auto-generated method stub
						
	}

	public void endReporting() {
		// TODO Auto-generated method stub
		
	}

	public boolean isActive() {
		// TODO Auto-generated method stub
		return true;
	}
	public boolean isError(){
		return this.problem.isError();
	}
	public IProblem getProblem(){
		return problem;
	}
	
}
