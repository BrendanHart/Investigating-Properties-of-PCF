The source code is verified to type check with Agda 2.6.0.1.

It can not be guaranteed that the source code for this project will not encounter errors, such as unknown flags or syntax errors, with other versions. 

The source code can be found under the `src` directory. The `.lagda` files in the report directory are literate Agda files are used to build the report, which can be compiled with the `./compile-report.sh` script.

Individual files can be type checked by running:

    $ agda <path-to-file>

This will also ensure any imported files are type checked. The output of this command should not produce any errors.

To verify the proof of correctness, after entering the directory with the source files, the command would be:

    $ agda PCF-With-Lambda-Correctness.lagda

For adequacy, it would be:

    $ agda PCF-With-Lambda-Adequacy.lagda

However, when exploring Agda code, we tend to use Emacs.

There is the Agda mode for Emacs which adds functionality to Emacs for interacting with Agda files, such as loading an opened Agda file.

Instructions for setting this up can be found at the <https://my-agda.readthedocs.io/en/latest/getting-started/installation.html>.

After opening an Agda file in Emacs, it can then be type checked with `Ctrl-c` `Ctrl-l`.

A more detailed list of the Agda mode for Emacs can be found at <https://agda.readthedocs.io/en/v2.6.0.1/tools/emacs-mode.html>.

Note that it can be expected to see some differences between the report and the Agda code. These are minor, and do not
change the proof. They are usually changes to aid the reader when relating the code in the report to the rest of the report,
or changes made to ensure the code fits within the pages.

It is also important to note that the source files do not solely contain developments from just this project. They include previous
work by Martín Escardó et al. which has been built upon. The author can be found at the top of each file. See <https://github.com/martinescardo/TypeTopology> for the latest developments.
