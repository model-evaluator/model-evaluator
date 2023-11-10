package model.function;

import org.javers.core.metamodel.annotation.DiffInclude;

import model.url.Url;

public class HistoryPushState extends Event {
	
	@DiffInclude
	public String tarUrl;
	
	@DiffInclude
	public String url;
	
	public HistoryPushState() {
		
	}

}
