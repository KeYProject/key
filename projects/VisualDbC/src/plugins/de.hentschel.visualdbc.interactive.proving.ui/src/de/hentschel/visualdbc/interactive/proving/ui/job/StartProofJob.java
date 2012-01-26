package de.hentschel.visualdbc.interactive.proving.ui.job;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.emf.edit.domain.EditingDomain;
import org.eclipse.gmf.runtime.diagram.ui.editparts.ShapeNodeEditPart;
import org.key_project.key4eclipse.util.eclipse.job.ObjectchedulingRule;

import de.hentschel.visualdbc.dbcmodel.DbcProof;
import de.hentschel.visualdbc.interactive.proving.ui.util.LogUtil;
import de.hentschel.visualdbc.interactive.proving.ui.util.ProofUtil;

/**
 * This {@link Job} starts a proof in interactive mode via
 * {@link ProofUtil#openProof(EditingDomain, DbcProof, ShapeNodeEditPart, IProgressMonitor)}.
 * @author Martin Hentschel
 */
public class StartProofJob extends Job {
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
      super("Start proof");
      setRule(new ObjectchedulingRule(getClass()));
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
   }
}
