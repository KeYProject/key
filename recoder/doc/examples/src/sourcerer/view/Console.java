package sourcerer.view;

import java.awt.Color;
import java.awt.Font;
import java.awt.event.KeyAdapter;
import java.awt.event.KeyEvent;
import java.io.PrintStream;
import java.io.Reader;
import java.util.Vector;

import javax.swing.BorderFactory;
import javax.swing.JTextArea;
import javax.swing.text.BadLocationException;

import recoder.ServiceConfiguration;
import sourcerer.Resources;
import bsh.ConsoleInterface;
import bsh.EvalError;
import bsh.Interpreter;

/**
   to do:
   Forbid to insert text after a bad mouse click into the forbidden zone.
   Forbid to cut() / paste() when the selection crosses the prompt barrier.
*/
public abstract class Console extends JTextArea implements ConsoleInterface {

    Interpreter interpreter;

    private PrintStream outStr;

    private static String PROMPT = "$ ";
    private static int HISTORY_SIZE = 100;
    private Vector cmdStack = new Vector(HISTORY_SIZE);
    private int cmdStackPos = -1;

    private int promptPosition = 0;
    private int promptLine = 0;


    public Console(ServiceConfiguration rsh) {
	setEditable(true);
	setLineWrap(true);
	// setBackground(SystemColor.inactiveCaptionText);
	setBackground(Color.white);
	setFont(new Font("Monospaced", Font.PLAIN, 12));
	setBorder(BorderFactory.createLoweredBevelBorder());
	addKeyListener(new KeyAdapter() {
		public void keyPressed(KeyEvent e) {
		    key(e);
		}

		public void keyReleased(KeyEvent e) {
		    key(e);
		}

		public void keyTyped(KeyEvent e) {
		    key(e);
		}

		private void key(KeyEvent e) {
		    switch (e.getKeyCode()) {
		    case KeyEvent.VK_LEFT:
		    case KeyEvent.VK_KP_LEFT:
		    case KeyEvent.VK_BACK_SPACE:
			if (getCaretPosition() <= promptPosition) {
			    e.consume();
			}
			break;
		    case KeyEvent.VK_PAGE_UP:
			if (e.getID() == KeyEvent.KEY_RELEASED) {
			    setCaretPosition(promptPosition);
			}
			e.consume();
			break;
		    case KeyEvent.VK_HOME:
			if (getCaretLine() == promptLine) {
			    if (e.getID() == KeyEvent.KEY_RELEASED) {
				setCaretPosition(promptPosition);
			    }
			    e.consume();			    
			}
			break;
		    case KeyEvent.VK_ENTER:			
			if (!e.isShiftDown()) {
			    if (e.getID() == KeyEvent.KEY_RELEASED) {
				evalCmd();
			    }
			    e.consume();
			} else {
			    if (e.getID() == KeyEvent.KEY_RELEASED) {
				replaceSelection("\n");
				// add proper prompt indentation?!
				// write multi-line prompts?
			    }
			}
			break;
		    case KeyEvent.VK_KP_UP:
		    case KeyEvent.VK_UP:
			if (getCaretLine() <= promptLine) {
			    if (e.getID() == KeyEvent.KEY_RELEASED) {
				if (cmdStackPos < cmdStack.size()-1) {
				    cmdStackPos++;
				    setCommand((String)cmdStack.elementAt(cmdStackPos));
				}
			    }
			    e.consume();
			}
			break;
		    case KeyEvent.VK_KP_DOWN:
		    case KeyEvent.VK_DOWN:
			if (getCaretLine() == getLineCount() - 1) {
			    if (e.getID() == KeyEvent.KEY_RELEASED) {
				if (cmdStackPos > 0) {
				    cmdStackPos--;
				    setCommand((String)cmdStack.elementAt(cmdStackPos));				
				} else if (cmdStackPos == 0) {
				    cmdStackPos = -1;
				    setCommand("");
				}
			    }
			    e.consume();
			}
			break;
		    case KeyEvent.VK_CLEAR:
		    case KeyEvent.VK_ESCAPE:
			if (e.getID() == KeyEvent.KEY_RELEASED) {
			    clear();
			    e.consume();
			}
			break;
		    default:
			switch (e.getKeyChar()) {
			case '\b':			    
			    if (getCaretPosition() <= promptPosition) {
				e.consume();
			    }
			    break;
			default:
			    if (getCaretPosition() < promptPosition) {
				e.consume();
			    }
			    break;
			}
			break;
		    }		    
		}
	    });
	interpreter = new Interpreter(this);
	try {
	    interpreter.eval(Resources.BEAN_SHELL_SCRIPT);
	    interpreter.set("rsh", rsh);
	} catch (EvalError ee) {
	    error(ee.toString());
	}
	printPrompt();
    }

    void setCommand(String newCommand) {
	replaceRange(newCommand, promptPosition, getDocument().getLength());
	setCaretPosition(getDocument().getLength());
    }

    void printPrompt() {
	append(PROMPT);
	promptPosition = getDocument().getLength();
	setCaretPosition(promptPosition);
	promptLine = getCaretLine();
	requestFocus();
    }

    int getCaretLine() {
	try {
	    return getLineOfOffset(getCaretPosition());
	} catch (BadLocationException ble) {
	    return 0; // cannot happen
	}
    }

    void evalCmd() {
	String command = getText().substring(promptPosition);
	append("\n");
	if (command.length() > 0) {
	    int s = cmdStack.size();
	    if (s == HISTORY_SIZE) {
		cmdStack.removeElementAt(HISTORY_SIZE-1);
	    }
	    if (s == 0 || !command.equals(cmdStack.elementAt(0))) {
		cmdStack.insertElementAt(command, 0);
	    }
	    cmdStackPos = -1;
	    processCommand(interpreter, command);
	}
	printPrompt();
    }

    public void clear() {
	cmdStackPos = -1;
	setText("");
	printPrompt();	
    }

    public Interpreter getInterpreter() {
	return interpreter;
    }

    protected abstract void processCommand(Interpreter interpreter, String command);

    // bsh console interface

    public PrintStream getOutputStream() {
        if (outStr == null) {
            outStr = new PrintStream(System.out) {
                public void print(String s) {
                    append(s);
                }
                public void println(String s) {
                    append(s);
		    append("\n");
                }
            };
        }
        return outStr;
    }

    public Reader getIn() {
        return null;
    }

    public PrintStream getOut() {
        return getOutputStream();
    }

    public PrintStream getErr() {
        return getOutputStream();
    }

    public void println(String s) {
        append(s);
	append("\n");
    }

    public void print(String s) {
        append(s);
    }

    public void error(String s) {
        append(s);
	append("\n");
    }
}


