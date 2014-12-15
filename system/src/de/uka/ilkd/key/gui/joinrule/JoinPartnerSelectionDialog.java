package de.uka.ilkd.key.gui.joinrule;

import java.awt.BorderLayout;
import java.awt.Dimension;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.ComponentAdapter;
import java.awt.event.ComponentEvent;
import java.awt.event.ItemEvent;
import java.awt.event.ItemListener;
import java.util.HashSet;

import javax.swing.BorderFactory;
import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JComboBox;
import javax.swing.JDialog;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.border.TitledBorder;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.util.Pair;

/**
 * JDialog for selecting one of several goals as a partner
 * for a join rule application.
 * 
 * @author Dominic Scheurer
 */
@SuppressWarnings("serial")
public class JoinPartnerSelectionDialog extends JDialog {

   private static final String CB_SELECT_CANDIDATE_HINT =
         "Select to add shown state as a join partner.";
   private static final Dimension INITIAL_SIZE =
         new Dimension(500, 300);
   
   private ImmutableList<Pair<Goal, PosInOccurrence>> candidates = null;
   private Services services = null;
   
   private HashSet<Pair<Goal, PosInOccurrence>> chosen =
         new HashSet<Pair<Goal,PosInOccurrence>>();
   
   private JTextArea txtPartner1 = null;
   private JTextArea txtPartner2 = null;
   private JComboBox cmbCandidates = null;
   private JCheckBox cbSelectCandidate = null;
   
   private JScrollPane scrpPartner1 = null;
   private JScrollPane scrpPartner2 = null;
   
   private JoinPartnerSelectionDialog() {
      super(
            MainWindow.getInstance(),
            "Select partner node for join operation",
            true);
      
      setLocation(MainWindow.getInstance().getLocation());
      
      // Text areas for goals to join
      txtPartner1 = new JTextArea("");
      txtPartner2 = new JTextArea("");
      txtPartner1.setEditable(false);
      txtPartner2.setEditable(false);
      
      scrpPartner1 = new JScrollPane(txtPartner1);
      scrpPartner2 = new JScrollPane(txtPartner2);
      
      // Goal selection dropdown field and checkbox
      cmbCandidates = new JComboBox();
      cmbCandidates.setMaximumSize(new Dimension(Integer.MAX_VALUE, 20));
      cmbCandidates.addItemListener(new ItemListener() {
         @Override
         public void itemStateChanged(ItemEvent e) {   
            Pair<Goal, PosInOccurrence> selectedCandidate =
                  getSelectedCandidate();
            
            txtPartner2.setText(LogicPrinter.quickPrintSequent(
                  selectedCandidate.first.sequent(), services));
            
            if (chosen.contains(selectedCandidate)) {
               cbSelectCandidate.setSelected(true);
            } else {
               cbSelectCandidate.setSelected(false);
            }
         }
      });
      addComponentListener(new ComponentAdapter() {
         @Override
         public void componentResized(ComponentEvent e) {
            super.componentResized(e);
            
            int halfWidth = getWidth() / 2;
            scrpPartner1.setPreferredSize(new Dimension(halfWidth, scrpPartner1.getHeight()));
            scrpPartner2.setPreferredSize(new Dimension(halfWidth, scrpPartner2.getHeight()));
         }
      });
      
      cbSelectCandidate = new JCheckBox();
      cbSelectCandidate.setToolTipText(CB_SELECT_CANDIDATE_HINT);
      cbSelectCandidate.addActionListener(new ActionListener() {
         @Override
         public void actionPerformed(ActionEvent e) {
            if (cbSelectCandidate.isSelected()) {
               chosen.add(getSelectedCandidate());
            } else {
               chosen.remove(getSelectedCandidate());
            }
         }
      });
      
      // Join state container
      JPanel joinStateContainer = new JPanel();
      joinStateContainer.setLayout(new BoxLayout(joinStateContainer, BoxLayout.Y_AXIS));
      joinStateContainer.add(scrpPartner1);
      
      TitledBorder joinStateContainerTitle =
            BorderFactory.createTitledBorder("State to join");
      joinStateContainerTitle.setTitleJustification(TitledBorder.LEFT);
      joinStateContainer.setBorder(joinStateContainerTitle);
      
      // Join partner container
      JPanel partnerContainer = new JPanel();
      partnerContainer.setLayout(new BoxLayout(partnerContainer, BoxLayout.Y_AXIS));
      partnerContainer.add(scrpPartner2);
      
      JPanel selectionContainer = new JPanel();
      selectionContainer.setLayout(new BoxLayout(selectionContainer, BoxLayout.X_AXIS));
      selectionContainer.add(cbSelectCandidate);
      selectionContainer.add(cmbCandidates);
      
      partnerContainer.add(selectionContainer);
      
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
      
      okButton.addActionListener(new ActionListener() {
         @Override
         public void actionPerformed(ActionEvent e) {
            setVisible(false);
         }
      });
      
      cancelButton.addActionListener(new ActionListener() {
         @Override
         public void actionPerformed(ActionEvent e) {
            chosen = null;
            setVisible(false);
         }
      });
      
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
      
      setSize(INITIAL_SIZE);
   }
   
   public JoinPartnerSelectionDialog(
         Goal joinNode,
         PosInOccurrence pio,
         ImmutableList<Pair<Goal,PosInOccurrence>> candidates,
         Services services) {
      
      this();
      this.candidates = candidates;
      this.services = services;
      
      txtPartner1.setText(LogicPrinter.quickPrintSequent(joinNode.sequent(), services));
      loadCandidates();
      
   }
   
   public ImmutableList<Pair<Goal, PosInOccurrence>> getChosen() {
      ImmutableSLList<Pair<Goal, PosInOccurrence>> result = ImmutableSLList.nil();
      
      if (chosen != null) {
         return result.append(chosen);
      } else {
         return result;
      }
   }
   
   private Pair<Goal, PosInOccurrence> getSelectedCandidate() {
      return getNthCandidate(cmbCandidates.getSelectedIndex());
   }
   
   private Pair<Goal, PosInOccurrence> getNthCandidate(int n) {
      int i = 0;
      for (Pair<Goal, PosInOccurrence> elem : candidates) {
         if (i == n) {
            return elem;
         }
         i++;
      }
      
      return null;
   }
   
   private void loadCandidates() {
      for (Pair<Goal, PosInOccurrence> candidate : candidates) {
         cmbCandidates.addItem("Node " + candidate.first.node().serialNr());
      }
      
      txtPartner2.setText(LogicPrinter.quickPrintSequent(
            candidates.head().first.sequent(), services));
   }
   
   public static void main(String[] args) {
      JoinPartnerSelectionDialog dialog = new JoinPartnerSelectionDialog();
      dialog.setVisible(true);
   }
   
}
