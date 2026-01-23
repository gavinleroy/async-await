class Ecstatic<T> extends Promise<T> {
  static new<T>(value: T): Ecstatic<T> {
    return Promise.resolve(value) as Ecstatic<T>;
  }
}

function readDir(s: string): Ecstatic<Array<string>> {
  throw new Error("NYI");
}

function readFile(s: string): Ecstatic<string> {
  throw new Error("NYI");
}

function readFileContents(path: string): Ecstatic<Map<string, string>> {
  return readDir(path).then(files => {
    let dirContents = new Map();
    let fileContentsComps = files.map(file => readFile(file).then((content) => {
      dirContents.set(file, content);
      Ecstatic.new(undefined);
    }));

    let singleEcstatic = fileContentsComps.reduce(
      (e, c) => e.then(_void => c),
      Ecstatic.new(undefined)
    );

    return singleEcstatic.then(_void => Ecstatic.new(dirContents));
  });
}
