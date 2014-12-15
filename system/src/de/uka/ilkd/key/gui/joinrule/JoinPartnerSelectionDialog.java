package de.uka.ilkd.key.gui.joinrule;

import java.awt.BorderLayout;
import java.awt.Dimension;

import javax.swing.BorderFactory;
import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JComboBox;
import javax.swing.JDialog;
import javax.swing.JPanel;
import javax.swing.JTextArea;
import javax.swing.border.TitledBorder;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Goal;

/**
 * JDialog for selecting one of several goals as a partner
 * for a join rule application.
 * 
 * @author Dominic Scheurer
 */
@SuppressWarnings("serial")
public class JoinPartnerSelectionDialog extends JDialog {

   private JTextArea txtPartner1 = null;
   private JTextArea txtPartner2 = null;
   private JComboBox cmbCandidates = null;
   
   private static final Dimension INITIAL_SIZE =
         new Dimension(500, 300);
   
   private JoinPartnerSelectionDialog() {
      super(
            MainWindow.getInstance(),
            "Select partner node for join operation",
            true);
      
      setSize(INITIAL_SIZE);
      
      setLocation(MainWindow.getInstance().getLocation());
      
      // Text areas for goals to join
      txtPartner1 = new JTextArea("");
      txtPartner2 = new JTextArea("");
      
      // Goal selection dropdown
      cmbCandidates = new JComboBox();
      
      // Join state container
      JPanel joinStateContainer = new JPanel();
      joinStateContainer.setLayout(new BoxLayout(joinStateContainer, BoxLayout.Y_AXIS));
      joinStateContainer.add(txtPartner1);
      
      TitledBorder joinStateContainerTitle =
            BorderFactory.createTitledBorder("State to join");
      joinStateContainerTitle.setTitleJustification(TitledBorder.LEFT);
      joinStateContainer.setBorder(joinStateContainerTitle);
      
      // Join partner container
      JPanel partnerContainer = new JPanel();
      partnerContainer.setLayout(new BoxLayout(partnerContainer, BoxLayout.Y_AXIS));
      partnerContainer.add(txtPartner2);
      partnerContainer.add(cmbCandidates);
      
      TitledBorder txtPartner2Title =
            BorderFactory.createTitledBorder("Potential join partners");
      txtPartner2Title.setTitleJustification(TitledBorder.LEFT);
      partnerContainer.setBorder(txtPartner2Title);
      
      // Upper container
      JPanel upperContainer = new JPanel();
      upperContainer.setLayout(new BoxLayout(upperContainer, BoxLayout.X_AXIS));
      upperContainer.add(joinStateContainer);
      upperContainer.add(partnerContainer);
      
      // Lower container: OK / Cancel
      JButton okButton = new JButton("OK");
      JButton cancelButton = new JButton("Cancel");
      okButton.setAlignmentX(CENTER_ALIGNMENT);
      cancelButton.setAlignmentX(CENTER_ALIGNMENT);
      
      JPanel lowerContainer = new JPanel();
      lowerContainer.setLayout(new BoxLayout(lowerContainer, BoxLayout.X_AXIS));
      lowerContainer.add(Box.createHorizontalGlue());
      lowerContainer.add(okButton);
      Dimension fillerDim = new Dimension(30, 40);
      lowerContainer.add(new Box.Filler(fillerDim, fillerDim, fillerDim));
      lowerContainer.add(cancelButton);
      lowerContainer.add(Box.createHorizontalGlue());
      
      // Add components to content pane
      getContentPane().add(upperContainer, BorderLayout.CENTER);
      getContentPane().add(lowerContainer, BorderLayout.SOUTH);
   }
   
   public JoinPartnerSelectionDialog(
         Goal joinNode, ImmutableList<Goal> candidates, Services services) {
      
      txtPartner1.setText(LogicPrinter.quickPrintSequent(joinNode.sequent(), services));
      
   }
   
   public static void main(String[] args) {
      JoinPartnerSelectionDialog dialog = new JoinPartnerSelectionDialog();
      dialog.setVisible(true);
   }
   
}
