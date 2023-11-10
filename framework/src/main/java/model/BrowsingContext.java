package model;

import java.util.ArrayList;
import java.util.List;

import org.javers.core.metamodel.annotation.Id;

import model.url.Origin;

public class BrowsingContext {
	
	@Id
	public String name;
	
	public Origin origin;
	
	public Document currentDoc;
	
	public List<BrowsingContext> nestedBcs;
	
	public List<History> sessionHistory;
	
	public Boolean isSecureContext;
	
	public Boolean isSandboxed;
	
	public Boolean sandboxWaitingNavigate;
	
	public List<BrowsingContext> opening;
	
	public List<Media> accesses;
	
	public Window win;
	
	public BrowsingContext(String _name, Boolean first) {
		
		this.name = _name;
		this.origin = model.url.StartupOrigin.getInstance();
		this.currentDoc = null;
		this.nestedBcs = new ArrayList<BrowsingContext>();
		this.sessionHistory = new ArrayList<History>();
		this.isSecureContext = false;
		this.isSandboxed = false;
		this.sandboxWaitingNavigate = false;
		this.opening = new ArrayList<BrowsingContext>();
		this.accesses = new ArrayList<Media>();
		
	}
	
	public BrowsingContext (String _name) {
		this.name = _name;
	}
	

}
