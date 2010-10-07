// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.gui;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;

import javax.swing.*;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.reuse.ReuseFindTaclet;
import de.uka.ilkd.key.proof.reuse.ReusePoint;
import de.uka.ilkd.key.proof.reuse.ReuseUpdateSimplificationRule;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.util.Debug;


public class ReuseListenerImpl implements ReuseListener, KeYSelectionListener {

   private KeYMediator medi;
   
   private List<ReusePoint> reusePoints;
   private ReusePoint best;
   
   private ReuseFindTaclet findTacletLogic;
   private ReuseUpdateSimplificationRule updateSimpRuleLogic;
   
   
   public ReuseListenerImpl(KeYMediator medi) {
      this.medi = medi;
      initLogicNewProof();
   }

   private void initLogicNewProof() {
      reusePoints = new LinkedList<ReusePoint>();
      findTacletLogic = new ReuseFindTaclet(medi, reusePoints);
      updateSimpRuleLogic = new ReuseUpdateSimplificationRule(medi, reusePoints);
   }
   
   
   
   public void selectedNodeChanged(KeYSelectionEvent e) {
      if (medi.autoMode()) return; // the strategy is running
      if (medi.reuseInProgress()) return; // we are still in the loop
      Node target = e.getSource().getSelectedNode();
      Node source = getPreImage(target);
      if (source != null) Main.getInstance().setStatusLine(
          "Template proof continues with: "+ source.name());
      else Main.getInstance().setStandardStatusLine();
//         source.getAppliedRuleApp().rule().name());
   }

   
   private Node getPreImage(Node target) {
      if (medi.getProof().getGoal(target) == null) return null; // inner node
      Node targetParent = target.parent();
      if (targetParent == null) return null;
      ReusePoint rp = targetParent.getReuseSource();
      if (rp == null) return null;
      int siblingNr = targetParent.getChildNr(target);
      try{
         return rp.source().child(siblingNr);
      } catch (Exception exc) {
      // there is no ruleApp at this point in the source proof (=open goal)
      // or IndexOutOfBounds because there is no such sibling in the template
      // forget about the hint then
          return null;
      }
   }
   
   Proof prevProof;
   
   public void showPreImage() {
       if (prevProof != null) {
           medi.setProof(prevProof);
           prevProof = null; // possible race here
           return;
       }
       prevProof = medi.getProof();
       Node curr = medi.getSelectedNode();
       Node pre = getPreImage(curr);
       if (pre==null) return;
       medi.setProof(pre.proof());
       medi.nonGoalNodeChosen(pre);
   }

   public void selectedProofChanged(KeYSelectionEvent e) {
      if (medi.getProof()==null) {
          medi.indicateNoReuse();
          return;
      }
      recomputeReuseTotal();
      if (reusePossible()) medi.indicateReuse(getBestReusePoint());
        else medi.indicateNoReuse();
   }


   
   public void recomputeReuseTotal() {
      initLogicNewProof();
      Iterator<Node> markerIt = Node.reuseCandidatesIterator();
      while (markerIt.hasNext()) {
         Node marker = markerIt.next();
          //         reuseLogger.info("***********************************************");
          for (Goal goal : medi.getProof().openGoals()) {
              analyzeCandidate(marker, goal);
          }
      }
   }



   
//remove RP with consumed goal
   public void removeRPConsumedGoal(Goal usedGoal) {
      ListIterator<ReusePoint> it = reusePoints.listIterator();
      while (it.hasNext()) {
         final ReusePoint rp = it.next();
         if ((rp.target()==usedGoal)) {
            it.remove();
         }
      }
   }


//add: old markers - new goals; call after removeRPConsumedMarker()
   public void addRPOldMarkersNewGoals(ImmutableList<Goal> newGoals) {
      if (newGoals==null) return; // dec. proc. return null as goal list
      Iterator<Node> markerIt = Node.reuseCandidatesIterator();
      while (markerIt.hasNext()) {
         Node marker = markerIt.next();
          for (Goal newGoal : newGoals) {
              analyzeCandidate(marker, newGoal);
          }
      }
   }


   
   
   public void removeRPConsumedMarker(Node usedMarker) {
      usedMarker.unmarkReuseCandidate();

//remove RP with consumed marker
      ListIterator<ReusePoint> it = reusePoints.listIterator();
      while (it.hasNext()) {
         ReusePoint rp = it.next();
         if ((rp.source()==usedMarker)) {
            it.remove();
         }
      }
   }


//add RP: new markers - all goals
   public void addRPNewMarkersAllGoals(Node usedMarker) {
      Iterator<Node> newMarkerIt = usedMarker.childrenIterator();
      while (newMarkerIt.hasNext()) {
         Node n = newMarkerIt.next();
         if ("Closed goal".equals(n.name())) continue; // this is ugly
         if ("OPEN GOAL".equals(n.name())) continue;
//         while ("Update Simplification".equals(n.name())) {
//            n = n.child(0);
//         }
         n.markReuseCandidate();
          //         reuseLogger.info("***********************************************");
          for (final Goal g : medi.getProof().openGoals()) {
              analyzeCandidate(n, g);
          }
      }
   }
   
   
   private ReusePoint highestScored(List<ReusePoint> l) {
      ReusePoint max = (ReusePoint) l.get(0);
      ListIterator<ReusePoint> it = l.listIterator();
      while (it.hasNext()) {
         ReusePoint curr = it.next();
         if (curr.score()>max.score()) max=curr;
      }
      return max;
   }



   public boolean reusePossible() {
      Debug.log4jWarn(">Possible applications detected: "+reusePoints.size(), "key.proof.reuse");
      if (reusePoints.size() > 0) {
         best = highestScored(reusePoints);
         return !best.notGoodEnough();
      } else {
         return false;
      }
   }

   
   public ReusePoint getBestReusePoint() {
       Debug.log4jInfo("############## RE-USING "+
           best.getApp().rule().name()+" "+best.score(), "key.proof.reuse");
       return best;
   }
   
   
   void analyzeCandidate(Node source, Goal target) {
      Debug.log4jInfo("***** (next goal) candidate nodes in system: "+
                       Node.reuseCandidatesNumber(), "key.proof.reuse");
//      reuseLogger.info("goal: "+target.node().sequent().toString()); //slow!
                       
      ReusePoint blank = new ReusePoint(source, target);
      if ( blank.getApp() == null ) return; // %%%%
      Rule r = blank.getApp().rule();
      if (r instanceof FindTaclet) {
          findTacletLogic.applicableWhere(blank);
      } else if (r instanceof NoFindTaclet) {
          NoPosTacletApp app = NoPosTacletApp.createNoPosTacletApp((Taclet)r);
	  ReusePoint p = blank.initializeNoFind(app, medi);
          if (p != null) { // RuleApp can be transferred // && goodEnough!
             reusePoints.add(p);
          }
      } else if (r instanceof BuiltInRule) {
          updateSimpRuleLogic.applicableWhere(blank);
      } else {
          String ruleName = blank.getApp().rule().getClass().toString();
          Debug.log4jError("Cannot re-use "+ruleName, "key.proof.reuse");
      }

   }
   
   private ListObjects guiList;
   
   public void startShowingState() {
       if (guiList == null) guiList = new ListObjects(reusePoints.toArray());
       else showState();
   }
   
   
   public void showState() {
       if (guiList!=null) {
           guiList.setListData(reusePoints.toArray());
           guiList.setVisible(true);
       }
   }
   
   
    public class ListObjects extends JFrame {
       JList menu2;
       JTextArea tf1;

       public ListObjects(Object[] content) {
          super("Breakfast Club Menu");
          menu2 = new JList(content);
          menu2.setSelectionMode(
             ListSelectionModel.MULTIPLE_INTERVAL_SELECTION);
          menu2.setSelectionBackground(java.awt.Color.YELLOW);
          menu2.setSelectionForeground(java.awt.Color.BLUE);

          //Register with listener
          menu2.addListSelectionListener(new ListSelectionListener() {
             public void valueChanged(ListSelectionEvent evt) {
                 ReusePoint rp = (ReusePoint) menu2.getSelectedValue();
	         tf1.setText((rp==null)? "" : rp.scoringInfo());
             }
          });

          //Text field to display JList selection
          tf1 = new JTextArea("Selection appears here . . .", 20,80);
          //Panel for JList object
          JPanel p2 = new JPanel();
	      p2.setBackground(java.awt.Color.WHITE);
	      //Add the list to the panel through
	      //a scrollpane
	      p2.add(new JScrollPane(menu2));
          //Panel for text field
	      JPanel p3 = new JPanel();
	      p3.setBackground(java.awt.Color.WHITE);
	      p3.add(tf1);

          getContentPane().add(p2, java.awt.BorderLayout.CENTER);
          getContentPane().add(p3, java.awt.BorderLayout.SOUTH);
          setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
//          setBounds(300, 400, 400, 300);
          pack();
          setVisible(true);
          setBackground(java.awt.Color.WHITE);
       }
       
       public void setListData(Object[] o) {
           menu2.setListData(o);
       }
       
       public void dispose() {
           guiList = null;
           super.dispose();
       }
    }
}
