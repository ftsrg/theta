package hu.bme.mit.inf.ttmc.statechart.ui;

import java.io.IOException;
import java.util.Collections;

import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.xtext.resource.XtextResource;
import org.eclipse.xtext.resource.XtextResourceSet;

import com.google.inject.Inject;
import com.google.inject.Injector;

import hu.bme.mit.inf.ttmc.statechart.language.StatechartLanguageStandaloneSetup;
import hu.bme.mit.inf.ttmc.statechart.model.StatechartModelPackage;
import hu.bme.mit.inf.ttmc.statechart.model.StatechartSpecification;

public class StatechartModelLoader {

	private static StatechartModelLoader instance;

	@Inject
	private XtextResourceSet resourceSet;

	private StatechartModelLoader() {
		final StatechartLanguageStandaloneSetup setup = new StatechartLanguageStandaloneSetup();
		final Injector injector = setup.createInjectorAndDoEMFRegistration();
		StatechartModelPackage.eINSTANCE.eClass();
		injector.injectMembers(this);
		resourceSet.addLoadOption(XtextResource.OPTION_RESOLVE_ALL, Boolean.TRUE);
	}

	public static StatechartModelLoader getInstance() {
		if (instance == null) {
			instance = new StatechartModelLoader();
		}
		return instance;
	}

	public StatechartSpecification load(final String filePath) {
		final URI uri = URI.createFileURI(filePath);
		final Resource resource = resourceSet.getResource(uri, true);
		final EObject object = resource.getContents().get(0);
		final StatechartSpecification specification = (StatechartSpecification) object;
		return specification;
	}

	public void save(final StatechartSpecification specification, final String fileName) throws IOException {
		final URI uri = URI.createFileURI(fileName);
		final Resource resource = resourceSet.createResource(uri);
		resource.getContents().add(specification);
		resource.save(Collections.EMPTY_MAP);
	}
}
