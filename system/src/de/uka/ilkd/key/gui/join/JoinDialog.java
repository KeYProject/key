package de.uka.ilkd.key.gui.join;

import java.awt.Dimension;
import java.util.LinkedList;
import java.util.List;

import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.DefaultListModel;
import javax.swing.JLabel;
import javax.swing.JList;
import javax.swing.JScrollPane;
import javax.swing.ListSelectionModel;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;

import de.uka.ilkd.key.gui.utilities.CheckedUserInput;
import de.uka.ilkd.key.gui.utilities.CheckedUserInput.CheckedUserInputInspector;
import de.uka.ilkd.key.gui.utilities.CheckedUserInput.CheckedUserInputListener;
import de.uka.ilkd.key.gui.utilities.InspectorForFormulas;
import de.uka.ilkd.key.gui.utilities.StdDialog;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.join.PredicateEstimator;
import de.uka.ilkd.key.proof.join.PredicateEstimator.Result;
import de.uka.ilkd.key.proof.join.ProspectivePartner;

public class JoinDialog extends StdDialog{


    private static final long serialVersionUID = 1L;
    private final     ContentPanel content;
    public JoinDialog(CheckedUserInputInspector inspector,List<ProspectivePartner> partnerList, Proof proof,
            PredicateEstimator estimator) {
        super("Joining",  5, false);
        content = new ContentPanel(inspector, partnerList, proof,estimator,new CheckedUserInputListener(){

            @Override
            public void userInputChanged(String input, boolean valid) {
                getOkayButton().setEnabled(valid);
                
            }
        
            });
        this.setContent(content);
        
    }
    
    
    private static class ContentPanel extends Box{
        private static final long serialVersionUID = 1L;
        
        private SequentViewer sequentViewer1;
        private SequentViewer sequentViewer2;
        private JList         choiceList;
        private CheckedUserInput predicateInput;
        private JLabel        joinHeadline;
        private JLabel        infoPredicate;
        private final CheckedUserInputInspector inspector;
        private final Proof proof;
        private final PredicateEstimator estimator;
     
       // private JTextPane    inputPredicate;
        
        private static class ContentItem{
            final ProspectivePartner partner;
            
            public ContentItem(ProspectivePartner partner) {
                super();
                this.partner = partner;
            }

            Sequent getSequent(){
               return partner.getNode(1).sequent();
            }
            
            @Override
            public String toString() {
                return "Goal "+ partner.getNode(1).serialNr();
            }
            
            public String getPredicateInfo(){
                return "Decision Predicate (true for Goal " + partner.getNode(0).serialNr() + ", false for Goal " + partner.getNode(1).serialNr()+")";
            }
            
            public String getPredicate(Proof proof){
                if(partner.getCommonPredicate() == null){
                    return "";
                }
                LogicPrinter printer = new LogicPrinter(new ProgramPrinter(), new NotationInfo(), proof.getServices());
                try{
                    
                    printer.printTerm(partner.getCommonPredicate());
                }catch (Throwable e){
                    new RuntimeException(e);
                }
                String result = printer.toString();
                if(result.endsWith("\n")){
                         result = result.substring(0, result.length()-1);
                }
                return result;
            }
        }
        
        
        public ContentPanel(CheckedUserInputInspector inspector,List<ProspectivePartner> partnerList,final Proof proof,
                PredicateEstimator estimator,
                CheckedUserInputListener listener) {
            super(BoxLayout.Y_AXIS);
            this.inspector = inspector;
            this.proof = proof;
            this.estimator = estimator;
            create();
            getPredicateInput().addListener(listener);
            getPredicateInput().addListener(new CheckedUserInputListener() {
                
                @Override
                public void userInputChanged(String input, boolean valid) {
                    if(valid){
                        getSelectedPartner().setCommonPredicate(InspectorForFormulas.translate(proof.getServices(), input));
                    }
                }
            });
       
          
            if(!partnerList.isEmpty()){
                fill(partnerList);
            }
       
        }    

        private void fill(List<ProspectivePartner> partnerList){
            getHeadline().setText("Join Goal " +partnerList.get(0).getNode(0).serialNr());
            getSequentViewer1().setSequent(partnerList.get(0).getNode(0).sequent(), proof.getServices());
            
            DefaultListModel model = new DefaultListModel();
            for(final ProspectivePartner partner : partnerList){
                model.addElement(new ContentItem(partner));
                Result result = estimator.estimate(partner, proof);
                partner.setCommonPredicate(result.getPredicate());
                partner.setCommonParent(result.getCommonParent());
  
             }
            
            getChoiceList().setModel(model);
            getChoiceList().setSelectedIndex(0);
            
            
        }
        
        private void selectionChanged(int index){
            if(index < 0 || index > getChoiceList().getModel().getSize()){
                return;
            }
            ContentItem item = (ContentItem) choiceList.getModel().getElementAt(index);
            getSequentViewer2().setSequent(item.getSequent(),proof.getServices());
   
            getPredicateInput().setInput(item.getPredicate(proof));
            getInfoPredicate().setText(item.getPredicateInfo());
        }
   
        
        private void create(){
       
            
            Box box = Box.createHorizontalBox();
          
          
            box.add(getHeadline());
            box.add(Box.createHorizontalGlue());
            
            
            this.add(Box.createVerticalStrut(5));
            this.add(box);
            this.add(Box.createVerticalStrut(5));
            
            
            box = Box.createHorizontalBox();
            box.add(new JScrollPane(getSequentViewer1()));
       
            this.add(box);
            this.add(Box.createVerticalStrut(5));
            
            box = Box.createHorizontalBox();
         
            JLabel label = new JLabel("with");
            label.setAlignmentX(LEFT_ALIGNMENT);
            label.setFont(this.getFont());
            box.add(label);
            box.add(Box.createHorizontalGlue());
            this.add(box);
            this.add(Box.createVerticalStrut(5));
           
            box = Box.createHorizontalBox();
         
            box.add(new JScrollPane(getChoiceList()));
            box.add(Box.createHorizontalStrut(5));
            
            Box vertBox = Box.createVerticalBox();
            vertBox.add(new JScrollPane(getSequentViewer2()));
            vertBox.add(Box.createVerticalStrut(5));
            
            Box horzBox = Box.createHorizontalBox();
            
            label = new JLabel("Decision Predicate");
            label.setAlignmentX(LEFT_ALIGNMENT);
            label.setFont(this.getFont());
            horzBox.add(getInfoPredicate());
            horzBox.add(Box.createHorizontalGlue());
            vertBox.add(horzBox);
            vertBox.add(getPredicateInput());
         //   vertBox.add(getInfoPredicate());
            
            box.add(vertBox);
            
            
            this.add(box);
            //this.add(Box.createVerticalStrut(5));
            
            //box = Box.createHorizontalBox();
            
            //box.add(getPredicateInput());
     
            //this.add(box);
            this.add(Box.createVerticalStrut(5));
           
            
             
        }
        
           
        private JLabel getInfoPredicate() {
            if(infoPredicate == null){
                infoPredicate = new JLabel(" ");
                infoPredicate.setFont(this.getFont());
            }
            return infoPredicate;
        }
        
        private CheckedUserInput getPredicateInput() {
            if(predicateInput == null){
                predicateInput = new CheckedUserInput(inspector,false);
            }
            return predicateInput;
        }

        private JList getChoiceList(){
            if(choiceList == null){
                    choiceList = new JList();
                    choiceList.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
                    choiceList.setPreferredSize(new Dimension(100,300));
                    choiceList.addListSelectionListener(new ListSelectionListener() {
                     
                     @Override
                     public void valueChanged(ListSelectionEvent e) {
                         
                         
                             selectionChanged(choiceList.getSelectedIndex());
                       
                             
                     }
             });
            }
            return choiceList;
         }
        
        private JLabel getHeadline(){
            if(joinHeadline == null){
                    joinHeadline = new JLabel("Join");
                    joinHeadline.setFont(this.getFont());
                    joinHeadline.setAlignmentX(LEFT_ALIGNMENT);
            }
            return joinHeadline;
        }
        
        
        private SequentViewer getSequentViewer1(){
                if(sequentViewer1 == null){
                        sequentViewer1 = new SequentViewer();
                        sequentViewer1.setPreferredSize(new Dimension(400,200));
                       
                }
                return sequentViewer1;
        }
        
        private SequentViewer getSequentViewer2(){
                if(sequentViewer2 == null){
                        sequentViewer2 = new SequentViewer();
                        sequentViewer2.setPreferredSize(new Dimension(300,300));
                }
                return sequentViewer2;
        }

        public ProspectivePartner getSelectedPartner() {
            int index = getChoiceList().getSelectedIndex();
            return ((ContentItem)getChoiceList().getModel().getElementAt(index)).partner;
        }
    
    }
    
    public ProspectivePartner getSelectedPartner(){
                
        return content.getSelectedPartner();
    }
    
    
    public static void main(String [] args){
         JoinDialog dialog = new JoinDialog(new CheckedUserInputInspector() {
            
            @Override
            public String check(String toBeChecked) {
                
                return toBeChecked.equals("test") ? null : "type test";
            }
        },new LinkedList<ProspectivePartner>(),null,null);
         dialog.setVisible(true);
    }
    

}
