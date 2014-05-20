import java.io.File;

import de.uka.ilkd.key.gui.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;
import de.uka.ilkd.key.util.ProofStarter;


public class Test {
   public static void main(String[] args) {
      KeYEnvironment<CustomConsoleUserInterface> env = KeYEnvironment.load(new File("D:\\Desktop\\CC\\project.key"), null, null);
      Proof proof = env.getLoadedProof();
      ProofStarter ps = new ProofStarter(true);
      ps.init(proof);
      ApplyStrategyInfo info = ps.start();
//      env.getUi().startAndWaitForAutoMode(proof);
      System.out.println(proof.openGoals().size());
      System.out.println(info);
   }
}
