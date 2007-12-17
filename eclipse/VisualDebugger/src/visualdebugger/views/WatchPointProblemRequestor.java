package visualdebugger.views;

import java.util.Iterator;
import java.util.LinkedList;

import org.eclipse.jdt.core.IProblemRequestor;
import org.eclipse.jdt.core.compiler.IProblem;

public class WatchPointProblemRequestor implements IProblemRequestor {

	private IProblem problem = null;
	private LinkedList<IProblem> problems = new LinkedList<IProblem>();

	public void acceptProblem(IProblem problem) {

		this.problem = problem;
		problems.add(problem);

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

	public boolean isError() {
		return this.problem.isError();
	}
	
	public boolean hasErrors() {

		Iterator<IProblem> i = problems.iterator();
		while (i.hasNext()) {
			IProblem ip = (IProblem) (i.next());
			if (ip.isError()){return true;}
		}
		return false;
	}

	public IProblem getProblem() {
		return problem;
	}

	public LinkedList<IProblem> getProblems() {
		return problems;
	}

}
