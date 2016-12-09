package org.key_project.keyide.ui.composite;

import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.swt.widgets.Text;
import org.eclipse.swt.widgets.ToolBar;
import org.eclipse.swt.widgets.ToolItem;
import org.key_project.keyide.ui.util.IProofNodeSearchSupport;
import org.key_project.keyide.ui.util.KeYImages;

import de.uka.ilkd.key.proof.Node;

/**
 * A {@link SearchComposite} allows to search {@link Node}s in the proof tree.
 * @author Martin Hentschel
 */
public class SearchComposite extends Composite {
   /**
    * The {@link IProofNodeSearchSupport} to use.
    */
   private final IProofNodeSearchSupport searchSupport;
   
   /**
    * The {@link Text} to define the search criteria.
    */
   private Text searchText;
   
   /**
    * The {@link ToolItem} to jump to the previous search result.
    */
   private ToolItem previousButton;
   
   /**
    * The {@link ToolItem} to jump to the next search result.
    */
   private ToolItem nextButton;
   
   /**
    * The {@link ToolItem} to close the search.
    */
   private ToolItem closeButton;

   /**
    * Constructor.
    * @param parent The parent {@link Composite}.
    * @param style The style to use.
    * @param searchSupport The {@link IProofNodeSearchSupport} to use.
    */
   public SearchComposite(Composite parent, int style, IProofNodeSearchSupport searchSupport) {
      super(parent, style);
      assert searchSupport != null;
      this.searchSupport = searchSupport;
      setLayout(new FillLayout());
      setLayout(new GridLayout(3, false));
      Label searchLabel = new Label(this, SWT.NONE);
      searchLabel.setText("&Search");
      searchText = new Text(this, SWT.BORDER);
      searchText.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      searchText.addModifyListener(new ModifyListener() {
         @Override
         public void modifyText(ModifyEvent e) {
            handleSearchTextModified(e);
         }
      });
      ToolBar toolbar = new ToolBar(this, SWT.FLAT);
      previousButton = new ToolItem(toolbar, SWT.PUSH);
      previousButton.setImage(KeYImages.getImage(KeYImages.JUMP_TO_PREVIOUS_SEARCH_RESULT));
      previousButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            jumpToPreviousResult();
         }
      });
      nextButton = new ToolItem(toolbar, SWT.PUSH);
      nextButton.setImage(KeYImages.getImage(KeYImages.JUMP_TO_NEXT_SEARCH_RESULT));
      nextButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            jumpToNextResult();
         }
      });
      new ToolItem(toolbar, SWT.SEPARATOR);
      closeButton = new ToolItem(toolbar, SWT.PUSH);
      closeButton.setImage(KeYImages.getImage(KeYImages.CLOSE_SEARCH));
      closeButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            closeSearch();
         }
      });
      Listener keyListener = new Listener() {
         @Override
         public void handleEvent(Event event) {
            handleKeYPressed(event);
         }
      };
      this.addListener(SWT.KeyDown, keyListener);
      searchLabel.addListener(SWT.KeyDown, keyListener);
      searchText.addListener(SWT.KeyDown, keyListener);
      previousButton.addListener(SWT.KeyDown, keyListener);
      nextButton.addListener(SWT.KeyDown, keyListener);
      closeButton.addListener(SWT.KeyDown, keyListener);
   }

   /**
    * When the text in {@link #searchText} has changed.
    * @param e The event.
    */
   protected void handleSearchTextModified(ModifyEvent e) {
      searchSupport.searchText(searchText.getText());
   }

   /**
    * When a key was pressed.
    * @param event The event.
    */
   protected void handleKeYPressed(Event event) {
      if (event.keyCode == SWT.ESC) {
         closeSearch();
      }
      else if (event.keyCode == SWT.CR || event.keyCode == SWT.LF) {
         if ((event.stateMask & SWT.SHIFT) != 0) {
            jumpToPreviousResult();
         }
         else {
            jumpToNextResult();
         }
      }
   }

   /**
    * Jumps to the previous search result.
    */
   public void jumpToPreviousResult() {
      searchSupport.jumpToPreviousResult();
   }

   /**
    * Jumps to the next search result.
    */
   public void jumpToNextResult() {
      searchSupport.jumpToNextResult();
   }

   /**
    * Closes the search.
    */
   public void closeSearch() {
      searchSupport.closeSearchPanel();
   }
   
   /**
    * Defines if the search result is empty or not.
    * @param empty {@code true} empty search result, {@code false} not empty search result.
    */
   public void setEmptySearchResult(boolean empty) {
      if (empty) {
         searchText.setBackground(getDisplay().getSystemColor(SWT.COLOR_RED));
      }
      else {
         searchText.setBackground(null);
      }
   }
}
