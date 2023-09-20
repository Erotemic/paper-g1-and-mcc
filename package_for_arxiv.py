#!/usr/bin/env python3

def main():
    import pathlib
    import zipfile
    dpath = pathlib.Path('.').resolve()
    dname = dpath.name

    fpaths_rel = [
        'arxiv.sty',
        'main.bbl',
        'main.tex',
        'references.bib',
        'orcid.pdf',
    ]
    zip_fpath = dname + '.zip'
    import os

    zip_fpath = pathlib.Path(zip_fpath)
    if zip_fpath.exists():
        os.unlink(zip_fpath)

    zfile = zipfile.ZipFile(zip_fpath, mode='w',
                            compression=zipfile.ZIP_DEFLATED, compresslevel=9)
    with zfile:
        for fpath_rel in fpaths_rel:
            print(f'package fpath_rel={fpath_rel}')
            zfile.write(fpath_rel)
    print(f'wrote zip_fpath={zip_fpath}')


if __name__ == '__main__':
    main()
