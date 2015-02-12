package org.key_project.key4eclipse.resources.util.event;

import java.util.List;

import org.eclipse.core.resources.IFile;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;

/**
 * Allows to observe changes made by {@link KeYResourcesUtil}.
 * @author Martin Hentschel
 */
public interface IKeYResourcePropertyListener {
   /**
    * The proof closed persistent property has changed via
    * {@link KeYResourcesUtil#setProofClosed(IFile, Boolean)}.
    * @param proofFile The changed proof file.
    * @param closed The new closed state.
    */
   public void proofClosedChanged(IFile proofFile, Boolean closed);
   
   /**
    * The proof recursion cycle persistent property has changed via
    * {@link KeYResourcesUtil#setProofRecursionCycle(IFile, List)}.
    * @param proofFile The changed proof file.
    * @param cycle The new recursion cycle or {@code null} if not part of a cycle.
    */
   public void proofRecursionCycleChanged(IFile proofFile, List<IFile> cycle);
}
