package org.key_project.keyide.ui.util;

import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Device;
import org.eclipse.swt.widgets.TreeItem;
import org.eclipse.ui.services.IDisposable;
import org.key_project.util.bean.Bean;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

/**
 * Manages the {@link Color}s used in a proof tree.
 * @author Martin Hentschel
 */
public class ProofTreeColorManager extends Bean implements IDisposable {
   /**
    * Property {@link #getClosedGoalColor()}.
    */
   public static final String CLOSED_GOAL_COLOR = "closedGoalColor";

   /**
    * Property {@link #getLinkedGoalColor()}.
    */
   public static final String LINKED_GOAL_COLOR = "linkedGoalColor";

   /**
    * Property {@link #getDisabledGoalColor()}.
    */
   public static final String DISABLED_GOAL_COLOR = "disabledGoalColor";

   /**
    * Property {@link #getOpenGoalColor()}.
    */
   public static final String OPEN_GOAL_COLOR = "openGoalColor";

   /**
    * Property {@link #getNodeWithNotesColor()}.
    */
   public static final String NODE_WITH_NOTES_COLOR = "nodeWithNotesColor";

   /**
    * Property {@link #getNodeWithActiveStatementColor()}.
    */
   public static final String NODE_WITH_ACTIVE_STATEMENT_COLOR = "nodeWithActiveStatementColor";

   /**
    * Property {@link #getFoundNodeColor()}.
    */
   public static final String FOUND_NODE_COLOR = "foundNodeColor";
   
   /**
    * The {@link Device} to use.
    */
   private final Device device;
   
   /**
    * Listens for color changes.
    */
   private final IPropertyChangeListener propertyListener = new IPropertyChangeListener() {
      @Override
      public void propertyChange(PropertyChangeEvent event) {
         handlePropertyChange(event);
      }
   };
   
   /**
    * The {@link Color}.
    */
   private Color closedGoalColor;

   /**
    * The {@link Color}.
    */
   private Color linkedGoalColor;

   /**
    * The {@link Color}.
    */
   private Color disabledGoalColor;

   /**
    * The {@link Color}.
    */
   private Color openGoalColor;

   /**
    * The {@link Color}.
    */
   private Color nodeWithNotesColor;

   /**
    * The {@link Color}.
    */
   private Color nodeWithActiveStatementColor;

   /**
    * The {@link Color}.
    */
   private Color foundNodeColor;
   
   /**
    * Optionally an {@link AbstractProofNodeSearch} to consider.
    */
   private AbstractProofNodeSearch search;
   
   /**
    * Constructor.
    * @param device The {@link Device} to use.
    */
   public ProofTreeColorManager(Device device) {
      this.device = device;
      this.closedGoalColor = new Color(device, KeYIDEPreferences.getClosedGoalColor());
      this.linkedGoalColor = new Color(device, KeYIDEPreferences.getLinkedGoalColor());
      this.disabledGoalColor = new Color(device, KeYIDEPreferences.getDisabledGoalColor());
      this.openGoalColor = new Color(device, KeYIDEPreferences.getOpenGoalColor());
      this.nodeWithNotesColor = new Color(device, KeYIDEPreferences.getNodeWithNotesColor());
      this.nodeWithActiveStatementColor = new Color(device, KeYIDEPreferences.getNodeWithActiveStatementColor());
      this.foundNodeColor = new Color(device, KeYIDEPreferences.getFoundNodeColor());
      KeYIDEPreferences.getStore().addPropertyChangeListener(propertyListener);
   }

   /**
    * When a preference has changed.
    * @param event The event.
    */
   protected void handlePropertyChange(PropertyChangeEvent event) {
      if (KeYIDEPreferences.CLOSED_GOAL_COLOR.equals(event.getProperty())) {
         Color oldValue = this.closedGoalColor;
         this.closedGoalColor = new Color(device, KeYIDEPreferences.getClosedGoalColor());
         firePropertyChange(CLOSED_GOAL_COLOR, oldValue, this.closedGoalColor);
      }
      else if (KeYIDEPreferences.LINKED_GOAL_COLOR.equals(event.getProperty())) {
         Color oldValue = this.linkedGoalColor;
         this.linkedGoalColor = new Color(device, KeYIDEPreferences.getLinkedGoalColor());
         firePropertyChange(LINKED_GOAL_COLOR, oldValue, this.linkedGoalColor);
      }
      else if (KeYIDEPreferences.DISABLED_GOAL_COLOR.equals(event.getProperty())) {
         Color oldValue = this.disabledGoalColor;
         this.disabledGoalColor = new Color(device, KeYIDEPreferences.getDisabledGoalColor());
         firePropertyChange(DISABLED_GOAL_COLOR, oldValue, this.disabledGoalColor);
      }
      else if (KeYIDEPreferences.OPEN_GOAL_COLOR.equals(event.getProperty())) {
         Color oldValue = this.openGoalColor;
         this.openGoalColor = new Color(device, KeYIDEPreferences.getOpenGoalColor());
         firePropertyChange(OPEN_GOAL_COLOR, oldValue, this.openGoalColor);
      }
      else if (KeYIDEPreferences.NODE_WITH_NOTES_COLOR.equals(event.getProperty())) {
         Color oldValue = this.nodeWithNotesColor;
         this.nodeWithNotesColor = new Color(device, KeYIDEPreferences.getNodeWithNotesColor());
         firePropertyChange(NODE_WITH_NOTES_COLOR, oldValue, this.nodeWithNotesColor);
      }
      else if (KeYIDEPreferences.NODE_WITH_ACTIVE_STATEMENT_COLOR.equals(event.getProperty())) {
         Color oldValue = this.nodeWithActiveStatementColor;
         this.nodeWithActiveStatementColor = new Color(device, KeYIDEPreferences.getNodeWithActiveStatementColor());
         firePropertyChange(NODE_WITH_ACTIVE_STATEMENT_COLOR, oldValue, this.nodeWithActiveStatementColor);
      }
      else if (KeYIDEPreferences.FOUND_NODE_COLOR.equals(event.getProperty())) {
         Color oldValue = this.foundNodeColor;
         this.foundNodeColor = new Color(device, KeYIDEPreferences.getFoundNodeColor());
         firePropertyChange(FOUND_NODE_COLOR, oldValue, this.foundNodeColor);
      }
   }

   /**
    * Returns the {@link Color}.
    * @return The {@link Color}.
    */
   public Color getClosedGoalColor() {
      return closedGoalColor;
   }

   /**
    * Returns the {@link Color}.
    * @return The {@link Color}.
    */
   public Color getLinkedGoalColor() {
      return linkedGoalColor;
   }

   /**
    * Returns the {@link Color}.
    * @return The {@link Color}.
    */
   public Color getDisabledGoalColor() {
      return disabledGoalColor;
   }

   /**
    * Returns the {@link Color}.
    * @return The {@link Color}.
    */
   public Color getOpenGoalColor() {
      return openGoalColor;
   }

   /**
    * Returns the {@link Color}.
    * @return The {@link Color}.
    */
   public Color getNodeWithNotesColor() {
      return nodeWithNotesColor;
   }

   /**
    * Returns the {@link Color}.
    * @return The {@link Color}.
    */
   public Color getNodeWithActiveStatementColor() {
      return nodeWithActiveStatementColor;
   }

   /**
    * Returns the found node {@link Color}.
    * @return The found node {@link Color}.
    */
   public Color getFoundNodeColor() {
      return foundNodeColor;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      KeYIDEPreferences.getStore().removePropertyChangeListener(propertyListener);
      if (closedGoalColor != null) {
         closedGoalColor.dispose();
      }
      if (linkedGoalColor != null) {
         linkedGoalColor.dispose();
      }
      if (disabledGoalColor != null) {
         disabledGoalColor.dispose();
      }
      if (openGoalColor != null) {
         openGoalColor.dispose();
      }
      if (nodeWithNotesColor != null) {
         nodeWithNotesColor.dispose();
      }
      if (nodeWithActiveStatementColor != null) {
         nodeWithActiveStatementColor.dispose();
      }
   }
   
   /**
    * Color the {@link TreeItem} of the given {@link Node}.
    * @param item The {@link TreeItem}.
    * @param node The {@link Node}.
    */
   public void colorProofTreeNode(TreeItem item, Node node) {
      if (item != null && node != null) {
         // Background color
         if (search != null) {
            if (search.containsResult(node)) {
               item.setBackground(getFoundNodeColor());
            }
            else {
               item.setBackground(null);
            }
         }
         else {
            item.setBackground(null);
         }
         // Foreground color
         if (node.leaf()) { // "A leaf of the proof"
            Proof proof = node.proof();
            if (!proof.isDisposed()) {
               Goal goal = proof.getGoal(node);
               if (goal == null || node.isClosed()) { // "A closed goal"
                  item.setForeground(getClosedGoalColor());
               }
               else {
                  if (goal.isLinked()) { // "Linked Goal"
                     item.setForeground(getLinkedGoalColor());
                  }
                  else if (!goal.isAutomatic()) { // "Disabled Goal"
                     item.setForeground(getDisabledGoalColor());
                  }
                  else { // "Open Goal"
                     item.setForeground(getOpenGoalColor());
                  }
               }
            }
            else {
               item.setForeground(null); // Default color, because proof is disposed.
            }
         }
         else { // "An inner node of the proof"
            if (node.getNodeInfo().getNotes() != null) {
               item.setForeground(getNodeWithNotesColor());
            }
            else if (node.getNodeInfo().getActiveStatement() != null) {
               item.setForeground(getNodeWithActiveStatementColor());
            }
            else {
               item.setForeground(null); // Default color
            }
         }
      }
   }

   /**
    * Returns the currently active search.
    * @return The currently active search.
    */
   public AbstractProofNodeSearch getSearch() {
      return search;
   }

   /**
    * Sets the currently active search.
    * @param search The currently active search.
    */
   public void setSearch(AbstractProofNodeSearch search) {
      this.search = search;
   }
}
