package model.function;

import org.javers.core.metamodel.annotation.DiffInclude;
import org.javers.core.metamodel.annotation.Id;

import model.BrowsingContext;

public class Function {
	
	@DiffInclude
	public String rootBc;
	
	@DiffInclude
	public String bc;
	
	@DiffInclude
	public String party;
	
	@DiffInclude
	public Event event;
	
	public Function() {
		
	}
	
	

}
