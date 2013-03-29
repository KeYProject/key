package org.key_project.keyide.ui.editor;

import org.eclipse.ui.menus.CommandContributionItem;
import org.eclipse.ui.menus.CommandContributionItemParameter;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.rule.TacletApp;


/**
 * A customized {@link CommandContributionItem} which contains a {@link TacletApp}, a {@link KeYMediator} and a {@link PosInSequent}.
 * 
 * @author Christoph Schneider, Niklas Bunzel, Stefan Käsdorf, Marco Drebing
 */
public class TacletCommandContributionItem extends CommandContributionItem {

   private TacletApp app;
   
   private KeYMediator mediator;
   
   private PosInSequent pos;
   
   public TacletApp getTacletApp(){
      return app;
   }
   
   public KeYMediator getMediator(){
      return mediator;
   }
   
   public PosInSequent getPosInSequent(){
      return pos;
   }
   
   
   /**
    * The constructor with the additional parameters.
    * @param contributionParameters - the {@link CommandContributionItemParameter}.
    * @param app - the {@link TacletApp}.
    * @param mediator - the {@link KeYMediator}.
    * @param pos - the {@link PosInSequent}.
    */
   public TacletCommandContributionItem(
         CommandContributionItemParameter contributionParameters, TacletApp app, KeYMediator mediator, PosInSequent pos) {
      super(contributionParameters);
      this.app = app;
      this.mediator = mediator;
      this.pos = pos;
   }

}
