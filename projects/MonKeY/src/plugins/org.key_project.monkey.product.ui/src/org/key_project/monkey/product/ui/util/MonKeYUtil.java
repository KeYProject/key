package org.key_project.monkey.product.ui.util;

import java.io.File;
import java.util.Arrays;
import java.util.Comparator;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.monkey.product.ui.model.MonKeYProof;
import org.key_project.monkey.product.ui.model.MonKeYProofResult;
import org.key_project.util.eclipse.swt.SWTUtil;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.ClassTree;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.speclang.Contract;

/**
 * Provides static utility methods for MonKeY.
 * @author Martin Hentschel
 */
public final class MonKeYUtil {
   /**
    * Forbid instances.
    */
   private MonKeYUtil() {
   }

   /**
    * Utility method which does the loading of the given location in KeY
    * and returns the instantiated {@link MonKeYProof}s.
    * @param monitor The {@link IProgressMonitor} to use.
    * @param location The location to load.
    * @param bootClassPath The boot class path to use or {@code null} to use default.
    * @param showKeYMainWindow Show KeY's main window?
    * @return The instantiated {@link MonKeYProof}s.
    * @throws Exception Occurred Exception.
    */
   public static List<MonKeYProof> loadSourceInKeY(IProgressMonitor monitor,
                                                   File location,
                                                   File bootClassPath,
                                                   boolean showKeYMainWindow) throws Exception {
      if (monitor == null) {
         monitor = new NullProgressMonitor();
      }
      monitor.beginTask("Loading in KeY", IProgressMonitor.UNKNOWN);
      InitConfig init = KeYUtil.internalLoad(location, null, bootClassPath, showKeYMainWindow);
      Services services = init.getServices();
      boolean skipLibraryClasses = true;
      // get all classes
      SWTUtil.checkCanceled(monitor);
      final Set<KeYJavaType> kjts = services.getJavaInfo().getAllKeYJavaTypes();
      monitor.beginTask("Filtering types", kjts.size());
      final Iterator<KeYJavaType> it = kjts.iterator();
      while (it.hasNext()) {
         SWTUtil.checkCanceled(monitor);
         KeYJavaType kjt = it.next();
         if (!(kjt.getJavaType() instanceof ClassDeclaration || 
               kjt.getJavaType() instanceof InterfaceDeclaration) || 
             (((TypeDeclaration)kjt.getJavaType()).isLibraryClass() && skipLibraryClasses)) {
            it.remove();
         }
         monitor.worked(1);
      }
      monitor.done();
      // sort classes alphabetically
      SWTUtil.checkCanceled(monitor);
      monitor.beginTask("Sorting types", IProgressMonitor.UNKNOWN);
      final KeYJavaType[] kjtsarr = kjts.toArray(new KeYJavaType[kjts.size()]);
      Arrays.sort(kjtsarr, new Comparator<KeYJavaType>() {
         public int compare(KeYJavaType o1, KeYJavaType o2) {
            return o1.getFullName().compareTo(o2.getFullName());
         }
      });
      monitor.done();
      // List all contracts
      SWTUtil.checkCanceled(monitor);
      List<MonKeYProof> proofs = new LinkedList<MonKeYProof>();
      monitor.beginTask("Analysing types", kjtsarr.length);
      for (KeYJavaType type : kjtsarr) {
          SWTUtil.checkCanceled(monitor);
          ImmutableSet<IObserverFunction> targets = services.getSpecificationRepository().getContractTargets(type);
          for (IObserverFunction target : targets) {
              ImmutableSet<Contract> contracts = services.getSpecificationRepository().getContracts(type, target);
              for (Contract contract : contracts) {
                  proofs.add(new MonKeYProof(type.getFullName(), ClassTree.getDisplayName(services, contract.getTarget()), contract.getDisplayName(), init, contract));
              }
          }
          monitor.worked(1);
      }
      return proofs;
   }
   
   /**
    * Computes the sums as statistics over all given {@link MonKeYProof}s.
    * @param proofs The given {@link MonKeYProof}s.
    * @return The computed sums.
    */
   public static MonKeYProofSums computeSums(List<MonKeYProof> proofs) {
      // Compute sums
      long branches = 0;
      long nodes = 0;
      long time = 0;
      int closedCount = 0;
      for (MonKeYProof proof : proofs) {
         branches += proof.getBranches();
         nodes += proof.getNodes();
         time += proof.getTime();
         if (MonKeYProofResult.CLOSED.equals(proof.getResult())) {
            closedCount ++;
         }
      }
      return new MonKeYProofSums(branches, nodes, time, closedCount, proofs.size());
   }
   
   /**
    * Represents the result of {@link MonKeYUtil#computeSums(List)}.
    * @author Martin Hentschel
    */
   public static class MonKeYProofSums {
      /**
       * The accumulated number of branches.
       */
      private long branches;

      /**
       * The accumulated number of nodes.
       */
      private long nodes;

      /**
       * The accumulated time.
       */
      private long time;

      /**
       * The number of closed proofs.
       */
      private int closedCount;

      /**
       * The number of proofs.
       */
      private int proofsCount;
      
      /**
       * Constructor.
       * @param branches The accumulated number of branches.
       * @param nodes The accumulated number of nodes.
       * @param time The accumulated time.
       * @param closedCount The number of closed proofs.
       * @param proofsCount The number of proofs.
       */
      public MonKeYProofSums(long branches, 
                             long nodes, 
                             long time, 
                             int closedCount, 
                             int proofsCount) {
         this.branches = branches;
         this.nodes = nodes;
         this.time = time;
         this.closedCount = closedCount;
         this.proofsCount = proofsCount;
      }

      /**
       * Returns the accumulated number of branches.
       * @return The accumulated number of branches.
       */
      public long getBranches() {
         return branches;
      }

      /**
       * Returns the accumulated number of nodes.
       * @return The accumulated number of nodes.
       */
      public long getNodes() {
         return nodes;
      }

      /**
       * Returns the accumulated time.
       * @return The accumulated time.
       */
      public long getTime() {
         return time;
      }

      /**
       * Returns the number of closed proofs.
       * @return The number of closed proofs.
       */
      public int getClosedCount() {
         return closedCount;
      }

      /**
       * Returns the number of proofs.
       * @return The number of proofs.
       */
      public int getProofsCount() {
         return proofsCount;
      }
   }
}
