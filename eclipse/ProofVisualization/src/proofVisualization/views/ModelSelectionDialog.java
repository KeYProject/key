package proofVisualization.views;

import java.util.ArrayList;

import org.eclipse.jface.viewers.ArrayContentProvider;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableColumn;
import org.eclipse.swt.widgets.Widget;
import org.eclipse.ui.dialogs.SelectionDialog;

import de.uka.ilkd.key.visualization.ExecutionTraceModel;
import de.uka.ilkd.key.visualization.VisualizationModel;

public class ModelSelectionDialog extends SelectionDialog implements Listener {

        private IStructuredContentProvider fContentProvider;
        private ILabelProvider fLabelProvider;
        private Object fInput;
        private TableViewer fTableViewer;
        private Button checkbox; 
        private ExecutionTraceModel[] traces;
        private ExecutionTraceModel[] filteredTraces;

        public ModelSelectionDialog(Shell parent,VisualizationModel visModel) {
                super(parent);
                traces = visModel.getExecutionTraces();
                filteredTraces= visModel.getInterestingExecutionTraces();
                fInput = traces;
                fContentProvider  = new ArrayContentProvider();
                fLabelProvider=new ExecutionTraceLabelProvider();
        }

       
        public void create() {
                setShellStyle(SWT.DIALOG_TRIM | SWT.RESIZE);
                super.create();
        }
  
        
        protected Control createDialogArea(Composite container) {
                Composite parent= (Composite) super.createDialogArea(container);
                createMessageArea(parent);
                fTableViewer= new TableViewer(parent, getTableStyle());
                
                Table table= fTableViewer.getTable();
                table.setHeaderVisible(true);
                table.setLinesVisible(true);
                table.setFont(parent.getFont());
             
                TableColumn column;
                column = new TableColumn(table, SWT.NONE,0);
                column.setWidth(250);
                column.setText("Java Program");
                
                column = new TableColumn(table, SWT.NONE,1);
                column.setWidth(75);
                column.setText("First Node");
                column = new TableColumn(table, SWT.NONE,2);
                column.setWidth(75);
                column.setText("Last Node");
                GridData gd= new GridData(GridData.FILL_BOTH);
                fTableViewer.setContentProvider(fContentProvider);
                fTableViewer.setLabelProvider(fLabelProvider);
                fTableViewer.setInput(fInput);
                checkbox = new Button(parent,SWT.CHECK);
                checkbox.setText("Filter uninteresting traces");
                checkbox.addListener(SWT.Selection,this);
                gd.heightHint= convertHeightInCharsToPixels(15);
                gd.widthHint= convertWidthInCharsToPixels(100);
                table.setLayoutData(gd);
                applyDialogFont(parent);
                return parent;
        }
        
        
        protected void okPressed() {
            // Get the input children.
            Object[] children = fContentProvider.getElements(fInput);

            // Build a one element list of the selected element.
            int selIndex = fTableViewer.getTable().getSelectionIndex();
            if (children != null) {
                ArrayList list = new ArrayList();
                list.add(children[selIndex]);
                setResult(list);
            }
            super.okPressed();
        }
        
        public void handleEvent(Event e) {
            Widget source = e.widget;
            if (source == checkbox) {
               if (!checkbox.getSelection()){
                   fInput = traces;
               } else {
                   fInput = filteredTraces;
               }
               fTableViewer.setInput(fInput);
               fTableViewer.refresh();
            }
           
         }
        
        protected int getTableStyle() {
                return SWT.SINGLE | SWT.H_SCROLL | SWT.V_SCROLL | SWT.BORDER;
        }
        
        class ExecutionTraceLabelProvider extends LabelProvider implements ITableLabelProvider{
            public String getText(Object obj) {
                return "unknown label";
            }
            
   
            public Image getImage(Object obj) {
                return null;
            }
            
            public Image getColumnImage(Object obj, int index) {
                return null;
            }
            
            public String getColumnText(Object obj, int index) {
                ExecutionTraceModel model = ((ExecutionTraceModel) obj);
                if (index == 0) {
                        return model.getFirstTraceElement().getProgram().toString().replaceAll("\n"," ");
                } else if (index == 1){
                    return ""+model.getFirstNode().serialNr();
                } else if (index == 2) {
                    return ""+model.getLastNode().serialNr();
                }
                return "UNKNOWN TABLE INDEX";

            }
        
        }
}

