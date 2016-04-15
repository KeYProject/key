package org.key_project.keyide.ui.editor;

import org.key_project.util.bean.IBean;

import de.uka.ilkd.key.pp.PosInSequent;

/**
 * Provides the needed functionality to observe {@link PosInSequent} changes.
 * @author Martin Hentschel
 */
public interface IPosInSequentProvider extends IBean {
   /**
    * Property {@link #getSelectedPosInSequent()}.
    */
   public static final String PROP_SELECTED_POS_IN_SEQUENT = "selectedPosInSequent";

   /**
    * Returns the selected {@link PosInSequent}.
    * @return The selected {@link PosInSequent}.
    */
   public PosInSequent getSelectedPosInSequent();
}