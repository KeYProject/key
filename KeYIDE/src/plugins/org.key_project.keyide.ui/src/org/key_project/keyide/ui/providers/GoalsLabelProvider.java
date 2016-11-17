package org.key_project.keyide.ui.providers;

import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.LabelProviderChangedEvent;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.graphics.Image;
import org.key_project.keyide.ui.util.KeYImages;
import org.key_project.keyide.ui.views.GoalsPage;
import org.key_project.keyide.ui.views.GoalsView;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.java.ObjectUtil;

import de.uka.ilkd.key.logic.SequentChangeInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.GoalListener;
import de.uka.ilkd.key.proof.Node;

/**
 * The {@link LabelProvider} to label the list of open {@link Goal}s on
 * the {@link GoalsPage} of a {@link GoalsView}.
 * @author Seena Vellaramkalayil
 */
public class GoalsLabelProvider extends LabelProvider {
   /**
    * The {@link Viewer} in which this {@link LabelProvider} is used.
    */
   private final Viewer viewer;
   
   /**
    * The observed {@link Goal}s.
    */
   private final ImmutableList<Goal> observedGoals;

   /**
    * Listen for changes on {@link #observedGoals}.
    */
   private final GoalListener goalListener = new GoalListener() {
      @Override
      public void sequentChanged(Goal source, SequentChangeInfo sci) {
      }

      @Override
      public void goalReplaced(Goal source, Node parent, ImmutableList<Goal> newGoals) {
      }

      @Override
      public void automaticStateChanged(Goal source, boolean oldAutomatic, boolean newAutomatic) {
         handleAutomaticStateChanged(source, oldAutomatic, newAutomatic);
      }
   };
   
   /**
    * Constructor.
    * @param viewer  The {@link Viewer} in which this label provider is used.
    * @param goals The {@link Goal}s to show.
    */
   public GoalsLabelProvider(Viewer viewer, ImmutableList<Goal> goals) {
      this.viewer = viewer;
      this.observedGoals = goals;
      if (observedGoals != null && !observedGoals.isEmpty()) {
         for (Goal goal : observedGoals) {
            goal.addGoalListener(goalListener);
         }
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      if (observedGoals != null && !observedGoals.isEmpty()) {
         for (Goal goal : observedGoals) {
            goal.removeGoalListener(goalListener);
         }
      }
      super.dispose();
   }
   
   /**
    * When the automatic state of a {@link Goal} has changed.
    * @param source The changed {@link Goal}.
    * @param oldAutomatic The old state.
    * @param newAutomatic The new state.
    */
   protected void handleAutomaticStateChanged(final Goal source, boolean oldAutomatic, boolean newAutomatic) {
      if (!viewer.getControl().isDisposed()) {
         viewer.getControl().getDisplay().syncExec(new Runnable() {
            @Override
            public void run() {
               if (!viewer.getControl().isDisposed()) {
                  fireLabelProviderChanged(new LabelProviderChangedEvent(GoalsLabelProvider.this, source));
               }
            }
         });
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getText(Object element) {
      if (element instanceof Goal) {
         Goal goal = (Goal) element;
         return getString(goal);
      }
      else {
         return ObjectUtil.toString(element);
         
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public Image getImage(Object element) {
      if (element instanceof Goal) {
         Goal goal = (Goal) element;
         if (goal.isAutomatic()) {
            return KeYImages.getImage(KeYImages.NODE);
         }
         else {
            return KeYImages.getImage(KeYImages.DISABLED_GOAL);
         }
      }
      else {
         return super.getImage(element);
      }
   }
   
   /**
    * static method to get the text to display in the viewer.
    * @param goal the {@link Goal} to be displayed
    * @return the text to be displayed
    */
   public static String getString(Goal goal) {
      return "(#" + goal.node().serialNr() + ") " + goal.toString();
   }
}
