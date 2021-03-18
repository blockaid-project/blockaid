CREATE TABLE users(
    uid INT PRIMARY KEY NOT NULL,
    about_me TEXT,
    activities TEXT,
    allowed_restrictions TEXT,
    name TEXT,
    sex TEXT,
    books TEXT,
    movies TEXT,
    music TEXT,
    birthday TEXT,
    birthday_date TEXT,
    contact_email TEXT,
    can_message BOOLEAN,
    can_post BOOLEAN,
    first_name TEXT,
    has_timeline BOOLEAN,
    install_type TEXT,
    interests TEXT,
    is_app_user BOOLEAN,
    is_blocked BOOLEAN,
    is_minor BOOLEAN,
    last_name TEXT,
    middle_name TEXT,
    name_format TEXT
);

CREATE TABLE friends(
    uid1 INT NOT NULL REFERENCES users(uid),
    uid2 INT NOT NULL
);

CREATE TABLE photos(
    pid INT PRIMARY KEY NOT NULL,
    src TEXT NOT NULL,
    owner INT NOT NULL REFERENCES users(uid),
    modified DATETIME NOT NULL
);

CREATE TABLE photo_tags(
    subject INT NOT NULL REFERENCES users(uid),
    pid INT NOT NULL REFERENCES photos(pid),
    created DATETIME NOT NULL,
    xcoord FLOAT NOT NULL,
    ycoord FLOAT NOT NULL
);