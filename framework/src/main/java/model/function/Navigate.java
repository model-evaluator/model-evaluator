package model.function;

import org.javers.core.metamodel.annotation.DiffInclude;

import model.Document;
import model.url.Url;

public class Navigate extends Event {
	
	@DiffInclude
	public String url;
	
	@DiffInclude
	public String response;
	
	@DiffInclude
	public String xFrameOption;
	
	public Navigate() {
		
	}

}
