// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.proof.io;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.event.ProofSaverEvent;
import de.uka.ilkd.key.proof.io.event.ProofSaverListener;
import de.uka.ilkd.key.util.KeYConstants;

/**
 * Saves a proof and provides useful methods for pretty printing
 * terms or programs.
 */
public class ProofSaver extends OutputStreamProofSaver {

   private final File file;

   /**
    * <p>
    * Contains all listener. 
    * </p>
    * <p>
    * They are used for instance by the Eclipse integration to refresh the
    * workspace when a proof file was saved.
    * </p>.
    */
   private static final List<ProofSaverListener> listeners = new LinkedList<ProofSaverListener>();
   
   public ProofSaver(Proof proof, String fileName, String internalVersion) {
      this(proof, new File(fileName), internalVersion);
   }
   
   public ProofSaver(Proof proof, File file) {
      this(proof, file, KeYConstants.INTERNAL_VERSION);
   }
   
   public ProofSaver(Proof proof, File file, String internalVersion) {
      super(proof, internalVersion);
      this.file = file;
   }

   protected void save(File file) throws IOException {
       save(new FileOutputStream(file));
   }

   public String save() throws IOException {
      String errorMsg = null;
      try {
         save(file);
      }
      catch (IOException ioe) {
         errorMsg = "Could not save \n" + filename() + ".\n";
         errorMsg += ioe.toString();
      }
      catch (NullPointerException npe) {
         errorMsg = "Could not save \n" + filename() + "\n";
         errorMsg += "No proof present?";
         npe.printStackTrace();
      }
      catch (RuntimeException e) {
         errorMsg = e.toString();
         e.printStackTrace();
      }
      fireProofSaved(new ProofSaverEvent(this, filename(), errorMsg));
      return errorMsg;
   }

   @Override
   protected String getBasePath() throws IOException {
       return computeBasePath(file);
   }
   
   /**
    * Computes the base path of the given proof {@link File}.
    * <p>
    * This method is used by {@link #getBasePath()} and by the Eclipse integration.
    * @param proofFile The proof {@link File}.
    * @return The computed base path of the given proof {@link File}.
    * @throws IOException Occurred Exception.
    */
   public static String computeBasePath(File proofFile) throws IOException {
       return proofFile.getCanonicalFile().getParentFile().getCanonicalPath();
   }

    /**
     * Adds the {@link ProofSaverListener}.
     * @param l The {@link ProofSaverListener} to add.
     */
    public static void addProofSaverListener(ProofSaverListener l) {
       if (l != null) {
          listeners.add(l);
       }
    }
    
    /**
     * Removes the {@link ProofSaverListener}.
     * @param l The {@link ProofSaverListener} to remove.
     */
    public static void removeProofSaverListener(ProofSaverListener l) {
       if (l != null) {
          listeners.remove(l);
       }
    }
    
    /**
     * Informs all listener about the event {@link ProofSaverListener#proofSaved(ProofSaverEvent)}.
     * @param e The event.
     */
    protected static void fireProofSaved(ProofSaverEvent e) {
       ProofSaverListener[] toInform = listeners.toArray(new ProofSaverListener[listeners.size()]);
       for (ProofSaverListener l : toInform) {
          l.proofSaved(e);
       }
    }
    
    private String filename(){
       return file.getAbsolutePath();
    }
}
