package org.key_project.keyide.ui.editor;

import org.eclipse.ui.menus.CommandContributionItem;
import org.eclipse.ui.menus.CommandContributionItemParameter;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.macros.ProofMacro;;;

/**
 * A customized {@link CommandContributionItem} which contains a {@link ProofMacro}, a {@link UserInterfaceControl}, a {@link Node} and a {@link PosInSequent}.
 * 
 * @author Anna Marie Filighera
 */
public class MacroCommandContributionItem extends CommandContributionItem {
   
   /**
    * The {@link Node} at which to apply the macro.
    */
   private final Node node;
   
   /**
    * The {@link ProofMacro} to apply.
    */
   private final ProofMacro macro;
   
   /**
    * The {@link UserInterfaceControl} to use.
    */
   private final UserInterfaceControl ui;
   
   /**
    * The {@link PosInSequent} to apply {@link ProofMacro} on.
    */
   private final PosInSequent pos;
   
   /**
    * The constructor with the additional parameters.
    * @param contributionParameters - the {@link CommandContributionItemParameter}.
    * @param macro - the {@link ProofMacro}.
    * @param node - the {@link Node}.
    * @param ui - the {@link UserInterfaceControl}.
    * @param pos - the {@link PosInSequent}.
    */
   public MacroCommandContributionItem(CommandContributionItemParameter contributionParameters, Node node, ProofMacro macro, UserInterfaceControl ui, PosInSequent pos) {
      super(contributionParameters);
      this.node = node;
      this.macro = macro;
      this.ui = ui;
      this.pos = pos;
   }
   
   /**
    * Returns the {@link ProofMacro} to apply.
    * @return The {@link ProofMacro} to apply.
    */
   public ProofMacro getMacro() {
      return macro;
   }
   
   /**
    * Returns the {@link UserInterfaceControl} to use.
    * @return The {@link UserInterfaceControl} to use.
    */
   public UserInterfaceControl getUi() {
      return ui;
   }
   
   /**
    * Returns the {@link PosInSequent} to apply {@link ProofMacro} on.
    * @return The {@link PosInSequent} to apply {@link ProofMacro} on.
    */
   public PosInSequent getPosInSequent() {
      return pos;
   }

   /**
    * Returns the {@link Node}.
    * @return The {@link Node}.
    */
   public Node getNode() {
      return node;
   }
}
