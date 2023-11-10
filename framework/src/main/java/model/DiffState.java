package model;

import java.util.ArrayList;
import java.util.List;

import org.javers.core.diff.changetype.InitialValueChange;
import org.javers.core.diff.changetype.ValueChange;
import org.javers.core.diff.changetype.container.ListChange;

import model.function.Event;

public class DiffState {
	
//	public State startState;
//	
//	public State endState;
	
//	public Window focusedWindow;
	
//	public String focusedEvent;
	
	public String rootBc;
	
	public String bc;
	
	public String party;
	
	public String event;
	
//	public Document document;
	
	public List<ListChange> listChanges;
	
	public List<InitialValueChange> initValueChanges;
	
	public List<ValueChange> valueChanges;
	
	public List<OriginChange> originChanges;
	
	
	public DiffState() {
		this.listChanges = new ArrayList<ListChange>();
		this.initValueChanges = new ArrayList<InitialValueChange>();
		this.valueChanges = new ArrayList<ValueChange>();
		this.originChanges = new ArrayList<OriginChange>();
//		this.focusedEvent = "";
//		this.focusedWindow = "";
	}
}