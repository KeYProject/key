package visualdebugger;

import org.eclipse.jdt.junit.ITestRunListener;

import de.uka.ilkd.key.visualdebugger.DebuggerEvent;
import de.uka.ilkd.key.visualdebugger.VisualDebugger;

public class VBTestRunListener implements ITestRunListener {

    public void testEnded(String testId, String testName) {
        // TODO Auto-generated method stub

    }

    public void testFailed(int status, String testId, String testName,
            String trace) {
  
        final int index = testName.indexOf("(");
        final String methodName = testName.substring(0, index);
        final String className = testName.substring(index+1, testName.length()-1);
  
        
        VisualDebugger.TestCaseIdentifier tci = VisualDebugger.getVisualDebugger().new TestCaseIdentifier(className,methodName);
        if (VisualDebugger.getVisualDebugger().getNodeForTC(className,methodName)!=null)
            VisualDebugger.getVisualDebugger().fireDebuggerEvent(new DebuggerEvent( DebuggerEvent.TEST_RUN_FAILED,
        tci));
         
      

    }

    public void testReran(String testId, String testClass, String testName,
            int status, String trace) {
        // TODO Auto-generated method stub

    }

    public void testRunEnded(long elapsedTime) {
        // TODO Auto-generated method stub

    }

    public void testRunStarted(int testCount) {
        // TODO Auto-generated method stub

    }

    public void testRunStopped(long elapsedTime) {
        // TODO Auto-generated method stub

    }

    public void testRunTerminated() {
        // TODO Auto-generated method stub

    }

    public void testStarted(String testId, String testName) {
        // TODO Auto-generated method stub

    }

}
