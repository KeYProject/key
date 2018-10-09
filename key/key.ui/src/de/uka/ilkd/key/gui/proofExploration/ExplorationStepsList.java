package de.uka.ilkd.key.gui.proofExploration;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import javax.swing.*;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;
import java.awt.*;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

public class ExplorationStepsList extends JFrame {

    DefaultListModel<Node> listModel = new DefaultListModel<>();


    public ExplorationStepsList(String title, Proof model) throws HeadlessException {
        super(title);
        createListModel(model);
        initialize();
    }

    private void createListModel(Proof model) {
        listModel.clear();
        Node root = model.root();
        List<Node> explorationNodes = collectAllExplorationSteps(root);
        explorationNodes.forEach(node -> listModel.addElement(node));

    }



    public List<Node> collectAllExplorationSteps(Node root) {
        ArrayList<Node> list = new ArrayList<>();
        findExplorationchildren(root, list);
        return list;
    }

    private void findExplorationchildren(Node n, ArrayList<Node> list) {
        if(n.leaf()){
            return;
        }
        if(n.getNodeInfo().isExploration()) {
            list.add(n);
        }
        Iterator<Node> nodeIterator = n.childrenIterator();

        while(nodeIterator.hasNext()){
            list.addAll(collectAllExplorationSteps(nodeIterator.next()));
        }

    }


   /* if(node.leftChild == null && node.rightChild == null) {
        System.out.println(path);
        return;

    } else {
        printPaths(node.leftChild,new ArrayList<Integer>(path));
        printPaths(node.rightChild,new ArrayList<Integer>(path));
    }
}*/


    public void initialize(){
        //create the model and add elements


        //create the list
        JList countryList = new JList<>(listModel);
        countryList.setCellRenderer(new MyCellrenderer());
        countryList.addListSelectionListener(new ListSelectionListener() {
            @Override
            public void valueChanged(ListSelectionEvent e) {
                if (!e.getValueIsAdjusting()) {
                    final List<String> selectedValuesList = countryList.getSelectedValuesList();
                    System.out.println(selectedValuesList);
                }
            }
        });

        add(new JScrollPane(countryList));

        this.setDefaultCloseOperation(JFrame.DISPOSE_ON_CLOSE);
        this.setTitle("JList Example");
        this.setSize(200, 200);
        this.setLocationRelativeTo(null);
        this.setVisible(true);

    }

    private class MyCellrenderer extends DefaultListCellRenderer {
        @Override
        public Component getListCellRendererComponent(JList<?> list, Object value, int index, boolean isSelected, boolean cellHasFocus) {
            JLabel listCellRendererComponent = (JLabel) super.getListCellRendererComponent(list, value, index, isSelected, cellHasFocus);
            Node n = (Node) value;
            listCellRendererComponent.setText(n.serialNr() + " "+ n.getAppliedRuleApp().rule().name());
            return listCellRendererComponent;
        }
    }
}
