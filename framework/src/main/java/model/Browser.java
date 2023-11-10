package model;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import model.function.Function;
import model.url.Url;
import model.url.ValidBlobUrl;

public class Browser {
	
	public List<Url> urls;
	
	public List<BrowsingContext> bcs;
	
	public HashMap<BrowsingContext, ValidBlobUrl> blobs;
	
	public List<Media> medias;
	
	public Function function;
	
	public Browser() {
		this.bcs = new ArrayList<BrowsingContext>();
		this.blobs = new HashMap<BrowsingContext, ValidBlobUrl>();
		this.medias = new ArrayList<Media>();
		this.urls  = new ArrayList<Url>();
	}

}
