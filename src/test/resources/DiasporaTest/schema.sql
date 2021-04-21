CREATE TABLE users(
    id INT PRIMARY KEY NOT NULL,
    username TEXT,
    serialized_private_key TEXT,
    getting_started BOOL,
    disable_mail BOOL,
    language TEXT,
    email TEXT,
    encrypted_password TEXT,
    reset_password_token TEXT,
    remember_created_at DATETIME,
    sign_in_count INT,
    current_sign_in_at DATETIME,
    last_sign_in_at DATETIME,
    current_sign_in_ip TEXT,
    last_sign_in_ip TEXT,
    created_at DATETIME,
    updated_at DATETIME,
    invited_by_id INT,
    authentication_token TEXT,
    unconfirmed_email TEXT,
    confirm_email_token TEXT,
    locked_at DATETIME,
    show_community_spotlight_in_stream BOOL,
    auto_follow_back BOOL,
    auto_follow_back_aspect_id INT,
    hidden_shareables TEXT,
    reset_password_sent_at DATETIME,
    last_seen DATETIME,
    remove_after DATETIME,
    export TEXT,
    exported_at DATETIME,
    exporting BOOL,
    strip_exif BOOL,
    exported_photos_file TEXT,
    exported_photos_at DATETIME,
    exporting_photos BOOL,
    color_theme TEXT,
    post_default_public BOOL,
    consumed_timestep INT,
    otp_required_for_login BOOL,
    otp_backup_codes TEXT,
    plain_otp_secret TEXT
);

CREATE TABLE people(
    id INT PRIMARY KEY NOT NULL,
    guid TEXT,
    diaspora_handle TEXT,
    serialized_public_key TEXT,
    owner_id INT,
    created_at DATETIME,
    updated_at DATETIME,
    closed_account BOOL,
    fetch_status INT,
    pod_id INT
);

CREATE TABLE posts(
    id INT PRIMARY KEY NOT NULL,
    author_id INT,
    public BOOL,
    guid TEXT,
    type TEXT,
    text TEXT,
    created_at DATETIME,
    updated_at DATETIME,
    provider_display_name TEXT,
    root_guid TEXT,
    likes_count INT,
    comments_count INT,
    o_embed_cache_id INT,
    reshares_count INT,
    interacted_at DATETIME,
    tweet_id TEXT,
    open_graph_cache_id INT,
    tumblr_ids TEXT
);

CREATE TABLE share_visibilities(
    id INT PRIMARY KEY NOT NULL,
    shareable_id INT,
    hidden BOOL,
    shareable_type TEXT,
    user_id INT
);

CREATE TABLE mentions(
    id INT PRIMARY KEY NOT NULL,
    mentions_container_id INT,
    person_id INT,
    mentions_container_type TEXT
);

CREATE TABLE comments(
    id INT PRIMARY KEY NOT NULL,
    text TEXT,
    commentable_id INT,
    author_id INT,
    guid TEXT,
    created_at DATETIME,
    updated_at DATETIME,
    likes_count INT,
    commentable_type TEXT
);

CREATE TABLE profiles(
    id INT PRIMARY KEY NOT NULL,
    diaspora_handle TEXT,
    first_name TEXT,
    last_name TEXT,
    image_url TEXT,
    image_url_small TEXT,
    image_url_medium TEXT,
    birthday DATE,
    gender TEXT,
    bio TEXT,
    searchable BOOL,
    person_id INT,
    created_at DATETIME,
    updated_at DATETIME,
    location TEXT,
    full_name TEXT,
    nsfw BOOL,
    public_details BOOL
);

CREATE TABLE photos(
    id INT PRIMARY KEY NOT NULL,
    author_id INT,
    public BOOL,
    guid TEXT,
    pending BOOL,
    text TEXT,
    remote_photo_path TEXT,
    remote_photo_name TEXT,
    random_string TEXT,
    processed_image TEXT,
    created_at DATETIME,
    updated_at DATETIME,
    unprocessed_image TEXT,
    status_message_guid TEXT,
    height INT,
    width INT
);

CREATE TABLE locations(
    id INT PRIMARY KEY NOT NULL,
    address TEXT,
    lat TEXT,
    lng TEXT,
    status_message_id INT,
    created_at DATETIME,
    updated_at DATETIME
);

CREATE TABLE polls(
    id INT PRIMARY KEY NOT NULL,
    question TEXT,
    status_message_id INT,
    status BOOL,
    guid TEXT,
    created_at DATETIME,
    updated_at DATETIME
);

CREATE TABLE participations(
    id INT PRIMARY KEY NOT NULL,
    guid TEXT,
    target_id INT,
    target_type TEXT,
    author_id INT,
    created_at DATETIME,
    updated_at DATETIME,
    count INT
);

CREATE TABLE likes(
    id INT PRIMARY KEY NOT NULL,
    positive BOOL,
    target_id INT,
    author_id INT,
    guid TEXT,
    created_at DATETIME,
    updated_at DATETIME,
    target_type TEXT
);

CREATE TABLE tags(
    id INT PRIMARY KEY NOT NULL,
    name TEXT,
    taggings_count INT
);

CREATE TABLE taggings(
    id INT PRIMARY KEY NOT NULL,
    tag_id INT,
    taggable_id INT,
    taggable_type TEXT,
    tagger_id INT,
    tagger_type TEXT,
    context TEXT,
    created_at DATETIME
);

CREATE TABLE notifications(
    id INT PRIMARY KEY NOT NULL,
    target_type TEXT,
    target_id INT,
    recipient_id INT,
    unread BOOL,
    created_at DATETIME,
    updated_at DATETIME,
    type TEXT,
    guid TEXT
);

CREATE TABLE conversations(
    id INT PRIMARY KEY NOT NULL,
    subject TEXT,
    guid TEXT,
    author_id INT,
    created_at DATETIME,
    updated_at DATETIME
);

CREATE TABLE conversation_visibilities(
    id INT PRIMARY KEY NOT NULL,
    conversation_id INT,
    person_id INT,
    unread INT,
    created_at DATETIME,
    updated_at DATETIME
);

CREATE TABLE roles(
    id INT PRIMARY KEY NOT NULL,
    person_id INT,
    name TEXT,
    created_at DATETIME,
    updated_at DATETIME
);

CREATE TABLE aspects(
    id INT PRIMARY KEY NOT NULL,
    name TEXT,
    user_id INT,
    created_at DATETIME,
    updated_at DATETIME,
    order_id INT,
    post_default BOOL
);

CREATE TABLE services(
    id INT PRIMARY KEY NOT NULL,
    type TEXT,
    user_id INT,
    uid INT,
    access_token TEXT,
    access_secret TEXT,
    nickname TEXT,
    created_at DATETIME,
    updated_at DATETIME
);

CREATE TABLE contacts(
    id INT PRIMARY KEY NOT NULL,
    user_id INT,
    person_id INT,
    created_at DATETIME,
    updated_at DATETIME,
    sharing BOOL,
    receiving BOOL
);

CREATE TABLE user_preferences(
    id INT PRIMARY KEY NOT NULL,
    email_type TEXT,
    user_id INT,
    created_at DATETIME,
    updated_at DATETIME
);

CREATE TABLE tag_followings(
    id INT PRIMARY KEY NOT NULL,
    tag_id INT,
    user_id INT,
    created_at DATETIME,
    updated_at DATETIME
);

CREATE TABLE reports(
    id INT PRIMARY KEY NOT NULL,
    item_id INT,
    item_type TEXT,
    reviewed BOOL,
    text TEXT,
    created_at DATETIME,
    updated_at DATETIME,
    user_id INT
);
