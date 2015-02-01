/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package de.hentschel.visualdbc.interactive.proving.ui.job;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.emf.edit.domain.EditingDomain;
import org.eclipse.gmf.runtime.diagram.ui.editparts.ShapeNodeEditPart;
import org.key_project.key4eclipse.starter.core.job.AbstractKeYMainWindowJob;

import de.hentschel.visualdbc.dbcmodel.DbcProof;
import de.hentschel.visualdbc.interactive.proving.ui.job.event.IStartProofJobListener;
import de.hentschel.visualdbc.interactive.proving.ui.job.event.StartProofJobEvent;
import de.hentschel.visualdbc.interactive.proving.ui.util.LogUtil;
import de.hentschel.visualdbc.interactive.proving.ui.util.ProofUtil;

/**
 * This {@link Job} starts a proof in interactive mode via
 * {@link ProofUtil#openProof(EditingDomain, DbcProof, ShapeNodeEditPart, IProgressMonitor)}.
 * @author Martin Hentschel
 */
public class StartProofJob extends AbstractKeYMainWindowJob {
   /**
    * Contains all available listeners.
    */
   public static List<IStartProofJobListener> listeners = new LinkedList<IStartProofJobListener>();
   
   /**
    * The {@link EditingDomain} to use.
    */
   private EditingDomain domain;
   
   /**
    * The {@link DbcProof} to open.
    */
   private DbcProof proof;
   
   /**
    * The proof to edit part if available and {@code null} otherwise.
    */
   private ShapeNodeEditPart proofEditPart;
   
   /**
    * Constructor.
    * @param domain The {@link EditingDomain} to use.
    * @param proof The {@link DbcProof} to open.
    * @param proofEditPart The proof to edit part if available and {@code null} otherwise.
    */
   public StartProofJob(EditingDomain domain,
                        DbcProof proof,
                        ShapeNodeEditPart proofEditPart) {
      super("Starting proof");
      this.domain = domain;
      this.proof = proof;
      this.proofEditPart = proofEditPart;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected IStatus run(IProgressMonitor monitor) {
      try {
         ProofUtil.openProof(domain, proof, proofEditPart, monitor);
         return Status.OK_STATUS;
      }
      catch (Exception e) {
         return LogUtil.getLogger().createErrorStatus(e);
      }
      finally {
         fireJobFinished(new StartProofJobEvent(this));
      }
   }
   
   /**
    * Adds the given {@link IStartProofJobListener}.
    * @param l The {@link IStartProofJobListener} to add.
    */
   public static void addStartProofJobListener(IStartProofJobListener l) {
      if (l != null) {
         listeners.add(l);
      }
   }
   
   /**
    * Removes the given {@link IStartProofJobListener}.
    * @param l The {@link IStartProofJobListener} to remove.
    */
   public static void removeStartProofJobListener(IStartProofJobListener l) {
      if (l != null) {
         listeners.remove(l);
      }
   }
   
   /**
    * Returns all available {@link IStartProofJobListener}s.
    * @return The available {@link IStartProofJobListener}s.
    */
   public static IStartProofJobListener[] getStartProofJobListeners() {
      return listeners.toArray(new IStartProofJobListener[listeners.size()]);
   }
   
   /**
    * Fires the event {@link IStartProofJobListener#jobFinished(StartProofJobEvent)}
    * to all registered {@link IStartProofJobListener}s.
    * @param e The event to fire.
    */
   protected static void fireJobFinished(StartProofJobEvent e) {
      IStartProofJobListener[] listeners = getStartProofJobListeners();
      for (IStartProofJobListener l : listeners) {
         l.jobFinished(e);
      }
   }
}